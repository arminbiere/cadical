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

{
  int remove;
  opts.log = true;
}

  stats.decompositions++;

  START (decompose);

  DFS * dfs = new DFS[2*(max_var + 1)];
  int * repr = new int[2*(max_var + 1)];
  ZERO (repr, int, 2*(max_var + 1));

  int non_trivial_sccs = 0, substituted = 0;
  int original = active_variables ();
  unsigned dfs_idx = 0;

  vector<int> work, scc;

  for (int root_idx = 1; root_idx <= max_var; root_idx++) {
    if (!active (root_idx)) continue;
    for (int root_sign = -1; root_sign <= 1; root_sign += 2) {
      int root = root_sign * root_idx;
      if (repr[vlit (root)]) continue;
      LOG ("root dfs search %d", root);
      assert (work.empty ());
      assert (scc.empty ());
      work.push_back (root);
      while (!work.empty ()) {
	int parent = work.back ();
	DFS & parent_dfs = dfs[vlit (parent)];
	if (parent_dfs.min == TRAVERSED) {		// skip traversed
	  assert (repr [vlit (parent)]);
	  work.pop_back ();
	} else {
	  assert (!repr [vlit (parent)]);
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
	    LOG ("post dfs search %d index %u minimum %u",
	      parent, parent_dfs.idx, new_min);
	    if (parent_dfs.idx == new_min) {
	      int other, size = 0;
	      do {
		assert (!scc.empty ());
		other = scc.back ();
		scc.pop_back ();
		dfs[vlit (other)].min = TRAVERSED;
		repr[vlit (other)] = parent;
		size++;
		if (other != parent) substituted++;
#ifdef LOGGING
		if (other == parent && size == 1)
		  LOG ("trivial size 1 scc with %d", parent);
		else
		  LOG ("literal %d in scc of %d", other, parent);
#endif
	      } while (other != parent);
	      LOG ("scc of %d has size %d", parent, size);
	      if (size > 1) non_trivial_sccs++;
	    } else parent_dfs.min = new_min;
	  } else {              			// pre-fix
	    dfs_idx++;
	    assert (dfs_idx < TRAVERSED);
	    parent_dfs.idx = parent_dfs.min = dfs_idx;
	    scc.push_back (parent);
	    LOG ("post dfs search %d index %u", parent, dfs_idx);
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

  VRB ("decompose",
    stats.decompositions,
    "%d non-trivial sccs, %d substituted %.2f%%",
    non_trivial_sccs, substituted, percent (substituted, original));

  size_t clauses_size = clauses.size (), garbage = 0, replaced = 0;
  for (size_t i = 0; !unsat && i < clauses_size; i++) {
    Clause * c = clauses[i];
    if (c->garbage) continue;
    int j, size = c->size;
    for (j = 0; j < size; j++) {
      const int lit = c->literals[j];
      if (repr [ vlit (lit) ] != lit) break;
    }
    if (j == size) continue;
    LOG (c, "substituting");
    assert (clause.empty ());
    bool satisfied = false;
    for (int k = 0; !satisfied && k < size; k++) {
      const int lit = c->literals[k];
      int tmp = val (lit);
      if (tmp > 0) satisfied = true;
      else {
	const int other = repr [vlit (lit)];
	tmp = val (other);
	if (tmp < 0) continue;
	else if (tmp > 0) satisfied = true;
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
    } else if (!clause.size ()) {
      LOG ("learned empty clause during decompose");
      learn_empty_clause ();
    } else if (clause.size () == 1) {
      LOG (c, "unit %d after substitution", clause[0]);
      learn_unit_clause (clause[0]);
      mark_garbage (c);
    } else if (j < 2) {
      LOG ("watched literal %d becomes %d at position %d",
        clause[j], repr [vlit (clause[j])], j);
    } else {
      LOG ("first substituted literal %d becomes %d at position %d",
        clause[j], repr [vlit (clause[j])], j);
    }
    for (size_t k = 0; k < clause.size (); k++) unmark (clause[k]);
    clause.clear ();
  }

  VRB ("decompose",
    stats.decompositions,
    "%ld clauses replaced %.2f%% producing %ld garbage %.2f%% clauses",
    replaced, percent (replaced, clauses_size),
    garbage, percent (garbage, replaced));

  erase_vector (scc);

  delete [] dfs;
  delete [] repr;

  {
    int remove;
    opts.log = false;
  }

  if (!unsat && propagated < trail.size () && !propagate ()) {
    LOG ("empty clause after propagating units from substitution");
    learn_empty_clause ();
  }

  report ('d');
  STOP (decompose);
}

}
