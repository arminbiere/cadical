#include "clause.hpp"
#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

bool Internal::subsuming () {
  if (!opts.subsume) return false;
  return stats.conflicts >= subsume_limit;
}

inline bool Internal::subsumes (Clause * c) {
  if (c->garbage) return false;
  stats.subchecks++;
  const const_literal_iterator end = c->end ();
  for (const_literal_iterator i = c->begin (); i != end; i++)
    if (marked (*i) <= 0) return false;
  return true;
}

inline int Internal::subsume (Clause * c) {
  if (c->garbage || c->size < 3) return 0;
  if (c->redundant && c->extended) return 0;
  int lit0 = c->literals[0];
  int lit1 = c->literals[1];
  size_t size0 = watches (lit0).size ();
  size_t size1 = watches (lit1).size ();
  size_t minsize = min (size0, size1);
  if (minsize > (size_t) opts.subsumelim) return 0;
  stats.subtried++;
  int minlit = size0 == minsize ? lit0 : lit1;
  LOG (c, "trying to subsume");
  LOG ("checking %ld clauses watching %d", (long) minsize, minlit);
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
  if (!d) return -1;
  LOG (c, "subsumed");
  LOG (d, "subsuming");
  stats.subsumed++;
  if (c->redundant) stats.subred++; else stats.subirr++;
  c->garbage = true;
  if (c->redundant || !d->redundant) return 1;
  LOG ("turning redundant subsuming clause into irredundant clause");
  d->redundant = false;
  stats.irredundant++;
  assert (stats.redundant);
  stats.redundant--;
  return 1;
}

void Internal::subsume () {
  subsume_limit = stats.conflicts + opts.subsumeinc;
  if (clauses.empty ()) return;
  START (subsume);
  int tried = 0, subsumed = 0, round = 0, tmp;
  size_t start = subsume_next;
  while (tried < opts.subsumetries) {
    if (subsume_next >= clauses.size ()) subsume_next = 0;
    if (subsume_next == start && round++) break;
    Clause * c = clauses[subsume_next++];
    if ((tmp = subsume (c))) tried++;
    if (tmp > 0) subsumed++;
  }
  VRB ("subsumed %d ouf of %d tried clauses %.2f",
    tried, subsumed, percent (subsumed, tried));
  STOP (subsume);
}

};
