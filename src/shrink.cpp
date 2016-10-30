#include "internal.hpp"
#include "macros.hpp"

namespace CaDiCaL {

void Internal::shrink_clause () {
  START (shrink);
  int_iterator j = clause.begin (), i;
  for (i = j; i != clause.end (); i++) {
    int root = *j++ = *i;
    assert (val (root) < 0);
    Watches & ws = watches (-root);
    bool remove = false;
    for (const_watch_iterator k = ws.begin ();
         !remove && k != ws.end ();
	 k++) {
      Clause * c = k->clause;
      if (c->garbage) continue;
      if ((size_t) c->size > clause.size ()) continue;
      bool failed = false;
      const_literal_iterator l;
      for (l = c->begin (); !failed && l != c->end (); l++) {
	int lit = *l;
	if (lit == -root) continue;
	if (!flags (lit).inclause ()) failed = true;
	else if (val (lit) >= 0) failed = true;
      }
      if (!failed) {
	LOG (c, "literal %d shrunken by", root);
	remove = true;
      }
    }
    if (remove) {
      stats.shrunken++;
      j--;
    } else flags (root).set (INCLAUSE);
  }
  clause.resize (j - clause.begin ());
  check_clause ();
  STOP (shrink);
}

};
