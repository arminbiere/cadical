#include "internal.hpp"
#include "clause.hpp"
#include "macros.hpp"

namespace CaDiCaL {

bool Internal::subsuming () {
  if (!opts.subsume) return false;
  return stats.conflicts >= subsume_limit;
}

inline bool Internal::subsumes (Clause * c) {
  if (c->garbage) return false;
  const const_literal_iterator end = c->end ();
  for (const_literal_iterator i = c->begin (); i != end; i++)
    if (marked (*i) <= 0) return false;
  return true;
}

inline void Internal::subsume (Clause * c) {
  if (c->garbage || c->size < 3) return;
  if (c->redundant && c->extended) return;
  int lit0 = c->literals[0];
  int lit1 = c->literals[1];
  size_t size0 = watches (lit0).size ();
  size_t size1 = watches (lit1).size ();
  size_t minsize = min (size0, size1);
  if (minsize > (size_t) opts.subsumelim) return;
  int minlit = size0 == minsize ? lit0 : lit1;
  LOG (c, "trying to subsume along %d with %ld occourrences",
    minlit, (long) minsize);
  const const_literal_iterator end = c->end ();
  for (const_literal_iterator i = c->begin (); i != end; i++) mark (*i);
  Watches & ws = watches (minlit);
  Clause * d = 0;
  for (const_watch_iterator i = ws.begin (); !d && i != ws.end (); i++)
    if (i->clause != c &&
        i->size < c->size &&
	marked (i->blit) > 0 &&
	subsumes (i->clause))
      d = i->clause;
  for (const_literal_iterator i = c->begin (); i != end; i++) unmark (*i);
  if (!d) return;
  LOG (c, "subsumed");
  LOG (d, "subsuming");
  stats.subsumed++;
  c->garbage = true;
  if (c->redundant || !d->redundant) return;
  LOG ("turning redundant subsuming clause into irredundant clause");
  d->redundant = false;
  stats.irredundant++;
  assert (stats.redundant);
  stats.redundant--;
}

void Internal::subsume () {
  subsume_limit = stats.conflicts + opts.subsumeinc;
  if (clauses.empty ()) return;
  START (subsume);
  if (subsume_next >= clauses.size ()) subsume_next = 0;
  Clause * c = clauses[subsume_next++];
  subsume (c);
  STOP (subsume);
}

};
