#include "internal.hpp"
#include "macros.hpp"

namespace CaDiCaL {

void Internal::mark_duplicated_binary_clauses_as_garbage () {
  START (deduplicate);
  assert (simplifying);
  assert (!level);
  assert (watches ());
  vector<int> stack;
  for (int idx = 1; idx <= max_var; idx++) {
    if (!active (idx)) continue;
    for (int sign = -1; sign <= 1; sign += 2) {
      const int lit = sign * idx;
      Watches & ws = watches (lit);
      const const_watch_iterator end = ws.end ();
      watch_iterator j = ws.begin ();
      const_watch_iterator i;
      assert (stack.empty ());
      for (i = j; i != end; i++) {
	Watch w = *j++ = *i;
	if (!w.binary) continue;
	int other = w.blit;
	const int tmp = marked (other);
	Clause * c = w.clause;
	if (tmp > 0) {
	  LOG (c, "found duplicated");
	  if (c->garbage) { j--; continue; }
	  if (!c->redundant) {
	    watch_iterator k;
	    for (k = ws.begin ();;k++) {
	      assert (k != i);
	      if (!k->binary) continue;
	      if (k->blit != other) continue;
	      Clause * d = k->clause;
	      if (d->garbage) continue;
	      c = d;
	      break;
	    }
	    *k = w;
	  }
	  LOG (c, "mark garbage duplicated");
	  stats.subsumed++;
	  stats.duplicated++;
	  mark_garbage (c);
	  j--;
	} else if (tmp < 0) {
	  // TODO resolve and produce unit ...
	} else {
	  if (c->garbage) continue;
	  mark (other);
	  stack.push_back (other);
	}
      }
      ws.resize (j - ws.begin ());
      while (!stack.empty ()) {
	unmark (stack.back ());
	stack.pop_back ();
      }
    }
  }
  report ('2', 0);
  STOP (deduplicate);
}

};
