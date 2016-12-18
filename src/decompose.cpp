#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

#include <climits>

namespace CaDiCaL {

#define TRAVERSED UINT_MAX

struct DFS {
  unsigned idx, min;
  DFS () : idx (0), min (0) { }
};

void Internal::decompose () {
  
  if (!opts.decompose) return;

  assert (!level);
  stats.decompositions++;

  START (decompose);

  DFS * dfs = new DFS[2*(max_var + 1)];
  int * reprs = new int[2*(max_var + 1)];
  ZERO (reprs, int, 2*(max_var + 1));

  int non_trivial_sccs = 0, substituted = 0;
  int original = active_variables ();
  unsigned dfs_idx = 0;

  vector<int> work, scc;

  for (int root_idx = 1; !unsat && root_idx <= max_var; root_idx++) {
    if (!active (root_idx)) continue;
    for (int root_sign = -1; !unsat && root_sign <= 1; root_sign += 2) {
      int root = root_sign * root_idx;
      if (dfs[vlit (root)].min == TRAVERSED) continue;
      LOG ("root dfs search %d", root);
      assert (work.empty ());
      assert (scc.empty ());
      work.push_back (root);
      while (!unsat && !work.empty ()) {
	int parent = work.back ();
	DFS & parent_dfs = dfs[vlit (parent)];
	if (parent_dfs.min == TRAVERSED) {		// skip traversed
	  assert (reprs [vlit (parent)]);
	  work.pop_back ();
	} else {
	  assert (!reprs [vlit (parent)]);
	  Watches & ws = watches (-parent);
	  const const_watch_iterator end = ws.end ();
	  const_watch_iterator i;
	  if (parent_dfs.idx) { 			// post-fix
	    work.pop_back ();
	    unsigned new_min = parent_dfs.min;
	    for (i = ws.begin (); i != end; i++) {
	      const Watch & w = *i;
	      if (!w.binary) continue;
	      const int child = w.blit;
	      if (!active (child)) continue;
	      const DFS & child_dfs = dfs[vlit (child)];
	      if (new_min > child_dfs.min) new_min = child_dfs.min;
	    }
	    LOG ("post-fix work dfs search %d index %u minimum %u",
	      parent, parent_dfs.idx, new_min);
	    if (parent_dfs.idx == new_min) {
	      int other, size = 0, repr = parent;
	      assert (!scc.empty ());
	      size_t j = scc.size ();
	      do {
		assert (j > 0);
		other = scc[--j];
		if (other == -parent) {
		  LOG ("both %d and %d in one scc", parent, -parent);
		  learn_empty_clause ();
		} else {
		  if (abs (other) < abs (repr)) repr = other;
		  size++;
		}
	      } while (!unsat && other != parent);
	      if (!unsat) {
		LOG ("scc of representative %d of size %d", repr, size);
		do {
		  assert (!scc.empty ());
		  other = scc.back ();
		  scc.pop_back ();
		  dfs[vlit (other)].min = TRAVERSED;
		  reprs[vlit (other)] = repr;
		  if (other != repr) {
		    substituted++;
		    LOG ("literal %d in scc of %d", other, repr);
		  }
		} while (other != parent);
		if (size > 1) non_trivial_sccs++;
	      }
	    } else parent_dfs.min = new_min;
	  } else {              			// pre-fix
	    dfs_idx++;
	    assert (dfs_idx < TRAVERSED);
	    parent_dfs.idx = parent_dfs.min = dfs_idx;
	    scc.push_back (parent);
	    LOG ("pre-fix work dfs search %d index %u", parent, dfs_idx);
	    for (i = ws.begin (); i != end; i++) {
	      const Watch & w = *i;
	      if (!w.binary) continue;
	      const int child = w.blit;
	      if (!active (child)) continue;
	      const DFS & child_dfs = dfs[vlit (child)];
	      if (child_dfs.idx) continue;
	      work.push_back (child);
	    }
	  }
	}
      }
    }
  }

  erase_vector (work);
  erase_vector (scc);
  delete [] dfs;

  for (int idx = 1; !unsat && idx <= max_var; idx++) {
    if (!active (idx)) continue;
    int other = reprs [ vlit (idx) ];
    if (other == idx) continue;
    assert (active (other));
    assert (reprs[vlit (-idx)] == -other);
    extension.push_back (0);
    extension.push_back (-idx);
    extension.push_back (other);
    extension.push_back (0);
    extension.push_back (idx);
    extension.push_back (-other);
  }

  VRB ("decompose",
    stats.decompositions,
    "%d non-trivial sccs, %d substituted %.2f%%",
    non_trivial_sccs, substituted, percent (substituted, original));

  size_t clauses_size = clauses.size (), garbage = 0, replaced = 0;
  for (size_t i = 0; !unsat && i < clauses_size; i++) {
    Clause * c = clauses[i];
    if (c->garbage) continue;
    int substituted, size = c->size;
    for (substituted = 0; substituted < size; substituted++) {
      const int lit = c->literals[substituted];
      if (reprs [ vlit (lit) ] != lit) break;
    }
    if (substituted == size) continue;
    int substituted_watch =
      (substituted < 2 ? c->literals[substituted] : 0);
    replaced++;
    LOG (c, "substituting");
    assert (clause.empty ());
    bool satisfied = false;
    int falsified_watch = 0;
    for (int k = 0; !satisfied && k < size; k++) {
      const int lit = c->literals[k];
      int tmp = val (lit);
      if (tmp > 0) satisfied = true;
      else if (tmp < 0) {
	if (clause.size () < 2 && !falsified_watch)
	  falsified_watch = lit;
	continue;
      } else {
	const int other = reprs [vlit (lit)];
	tmp = val (other);
	if (tmp < 0) {
	  if (clause.size () < 2 && !falsified_watch)
	    falsified_watch = lit;
	  continue;
	} else if (tmp > 0) satisfied = true;
	else {
	  tmp = marked (other);
	  if (tmp < 0) satisfied = true;
	  else if (!tmp) {
	    mark (other);
	    clause.push_back (other);
	  }
	}
      }
    }
    if (satisfied) {
      LOG (c, "satisfied after substitution");
      mark_garbage (c);
      garbage++;
    } else if (!clause.size ()) {
      LOG ("learned empty clause during decompose");
      learn_empty_clause ();
    } else if (clause.size () == 1) {
      LOG (c, "unit %d after substitution", clause[0]);
      assign_unit (clause[0]);
      mark_garbage (c);
      garbage++;
    } else if (1) { // substituted_watch || falsified_watch) {
      {
	int make_it_optional;
      }
      if (substituted_watch)
	LOG ("watched literal %d becomes %d",
	  substituted_watch, reprs [vlit (substituted_watch)]);
      else
	LOG ("falsified watched literal %d", falsified_watch);
      size_t d_clause_idx = clauses.size ();
      Clause * d = new_substituted_clause (c);
      assert (clauses[d_clause_idx] = d);
      swap (clauses[i], clauses[d_clause_idx]);
      mark_garbage (c);
      garbage++;
    } else {
      LOG ("shrinking since watches are not substituted nor falsified");
      assert (c->size > 2);
      size_t l;
      for (l = 2; l < clause.size (); l++)
	c->literals[l] = clause[l];
      c->literals[l] = 0;
      c->size = l;
      c->update_after_shrinking ();
      LOG (c, "substituted");
    }
    while (!clause.empty ()) {
      int lit = clause.back ();
      clause.pop_back ();
      assert (marked (lit) > 0);
      unmark (lit);
    }
  }

  VRB ("decompose",
    stats.decompositions,
    "%ld clauses replaced %.2f%% producing %ld garbage %.2f%% clauses",
    replaced, percent (replaced, clauses_size),
    garbage, percent (garbage, replaced));

  erase_vector (scc);

  if (!unsat && propagated < trail.size () && !propagate ()) {
    LOG ("empty clause after propagating units from substitution");
    learn_empty_clause ();
  }

  for (int idx = 1; !unsat && idx <= max_var; idx++) {
    if (!active (idx)) continue;
    int other = reprs [ vlit (idx) ];
    if (other == idx) continue;
    assert (active (other));
    flags (idx).status = Flags::SUBSTITUTED;
    stats.substituted++;
  }

  delete [] reprs;
  
  flush_all_occs_and_watches ();
  report ('d');
  STOP (decompose);
}

}
