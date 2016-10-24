#include "clause.hpp"
#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// For certain instances it happens quite frequently that learned clauses
// backward subsume some of the recently learned clauses.  Thus whenever we
// learn a clause, we can eagerly check whether the last 'opts.sublast'
// learned clauses are subsumed by the new learned clause. This observation
// and the idea for this code is due to Donald Knuth (even though he
// originally only tried to subsume the very last clause).  Note that
// 'backward' means the learned clause from which we start the subsumption
// check is checked for subsuming earlier (larger) clauses.

// Check whether the marked 'Internal.clause' subsumes the argument.

inline bool Internal::eagerly_subsume_last_learned (Clause * c) {
  const_literal_iterator end = c->end ();
  size_t found = 0, remain = c->size - clause.size ();
  for (const_literal_iterator i = c->begin (); i != end; i++) {
    int tmp = marked (*i);
    if (tmp < 0) break;
    else if (tmp > 0) found++;
    else if (!remain--) break;
  }
  assert (found <= clause.size ());
  if (found < clause.size ()) return false;
  LOG (c, "learned clauses eagerly subsumes");
  assert (c->redundant);
  c->garbage = true;
  stats.sublast++;
  return true;
}

// Go over the last 'opts.sublast' clauses and check whether they are
// subsumed by the new clause in 'Internal.clause'.

void Internal::eagerly_subsume_last_learned () {
  START (sublast);
  const_int_iterator k;
  for (k = clause.begin (); k != clause.end (); k++) mark (*k);
  const_clause_iterator i = clauses.end ();
  int subsumed = 0, tried = 0;
  for (int j = 0; j < opts.sublast; j++) {
    if (i == clauses.begin ()) break;
    Clause * c = *--i;
    if (c->garbage) continue;
    if (!c->redundant) continue;
    if ((size_t) c->size <= clause.size ()) continue;
    LOG (c, "trying to eagerly subsume");
    if (eagerly_subsume_last_learned (c)) subsumed++;
    tried++;
  }
  for (k = clause.begin (); k != clause.end (); k++) unmark (*k);
  LOG ("subsumed eagerly %d clauses out of %d tried", subsumed, tried);
  STOP (sublast);
}

/*------------------------------------------------------------------------*/

// This section contains a global forward subsumption algorithm, which is
// run frequently during search.  More specifically it is run in phases
// every 'opts.subsumeinc' conflicts and then in each phase tries to subsume
// the next 'opts.subsumetries' clauses.  It works both on original
// (irredundant) clauses and on 'sticky' learned clauses which are small
// enough or have a small enough glue to be otherwise kept forever (see
// 'opts.keepsize' and 'opts.keeglue', e.g., a redundant clause is not
// extended and thus kept if its size is smaller equal to 'opts.keepsize' or
// its glue is smaller equal than 'opts.keepsize').  Note, that 'forward'
// means that the clause from which the sumption check is started is checked
// for being subsumed by other (smaller or equal size) clauses.

bool Internal::subsuming () { if (!opts.subsume) return false; return
stats.conflicts >= subsume_limit;
}

inline bool Internal::subsume_check (Clause * c) {
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
    if (i->clause != c &&          // ignore starting clause of course
        i->size <= c->size &&      // smaller or identically sized
	marked (i->blit) > 0 &&    // blocking literal has to in 'c'
	subsume_check (i->clause)) // then really check subsumption
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
