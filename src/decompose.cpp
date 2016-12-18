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

  stats.decompositions++;

  START (decompose);

  DFS * dfs = new DFS[2*(max_var + 1)];
  int * repr = new int[2*(max_var + 1)];
  ZERO (repr, int, 2*(max_var + 1));

  int non_trivial_sccs = 0, substituted = 0, original = active_variables ();
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
#ifdef LOGGIGN
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

  erase_vector (scc);

  delete [] dfs;
  delete [] repr;

  report ('d');
  STOP (decompose);
}

}
