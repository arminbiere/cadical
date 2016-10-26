#include "clause.hpp"
#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "proof.hpp"

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
  mark_clause ();
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
  unmark_clause ();
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

bool Internal::subsuming () {
  if (!opts.subsume) return false;
  return stats.conflicts >= lim.subsume;
}

inline int Internal::subsume_check (Clause * c) {
  if (c->garbage) return false;
  stats.subchecks++;
  const const_literal_iterator end = c->end ();
  int flipped = 0;
  for (const_literal_iterator i = c->begin (); i != end; i++) {
    const int lit = *i, tmp = marked (lit);
    if (!tmp) return 0;
    if (tmp > 0) continue;
    if (flipped) return 0;
    flipped = lit;
  }
  return flipped ? flipped : INT_MIN;
}

inline void Internal::strengthen_clause (Clause * c, int remove) {
  stats.strengthened++;
  assert (c->size > 2);
  LOG (c, "removing %d in", remove);
  if (proof) proof->trace_strengthen_clause (c, remove);
  const int l0 = c->literals[0], l1 = c->literals[1];
  unwatch_literal (l0, c), unwatch_literal (l1, c);
  const const_literal_iterator end = c->end ();
  literal_iterator j = c->begin ();
  for (const_literal_iterator i = j; i != end; i++)
    if ((*j++ = *i) == remove) j--;
  assert (j + 1 == end);
  dec_bytes (sizeof (int));;
  c->size--;
  if (c->redundant && c->glue > c->size) c->glue = c->size;
  if (c->extended) c->resolved () = ++stats.resolved;
  LOG (c, "strengthened");
  watch_literal (c->literals[0], c->literals[1], c, c->size);
  watch_literal (c->literals[1], c->literals[0], c, c->size);
}

inline int Internal::subsume (Clause * c) {

  if (c->garbage) return 0;
  if (c->size < 3) return 0;	// do not subsume binary clauses

  // Redundant and extended clauses are subject to being recycled in
  // 'reduce' and thus not checked for being forward subsumed here.
  //
  if (c->redundant && c->extended) return 0;

  // Find literal in 'c' with smallest watch list.
  //
  const const_literal_iterator end = c->end ();
  size_t minsize = 0;
  int minlit = 0;
  for (const_literal_iterator i = c->begin (); i != end; i++) {
    int lit = *i;
    size_t size = watches (lit).size ();
    if (minlit && size >= minsize) continue;
    minlit = lit, minsize = size;
  }
  if (minsize > (size_t) opts.subsumelim) return 0;

  stats.subtried++;
  LOG (c, "trying to subsume");
  LOG ("checking %ld clauses watching %d", (long) minsize, minlit);

  mark (c);

  // Go over the clauses of the watched literal with less watches.
  //
  Watches & ws = watches (minlit);
  Clause * d = 0;
  int flipped = 0;
  for (const_watch_iterator i = ws.begin (); !d && i != ws.end (); i++)
    if (i->clause != c &&          // ignore starting clause of course
        i->size <= c->size &&      // smaller or identically sized
	marked (i->blit) > 0 &&    // blocking literal has to in 'c'
	(flipped = subsume_check (i->clause)))
      d = i->clause;

  unmark (c);

  if (flipped == INT_MIN) {
    stats.subsumed++;
    LOG (d, "subsuming");
    LOG (c, "subsumed");
    if (c->redundant) stats.subred++; else stats.subirr++;
    c->garbage = true;
    if (c->redundant || !d->redundant) return 1;

    LOG ("turning redundant subsuming clause into irredundant clause");
    d->redundant = false;
    stats.irredundant++;
    assert (stats.redundant);
    stats.redundant--;
  } else if (flipped && opts.strengthen && var (flipped).reason != c) {
    LOG (d, "self-subsuming");
    strengthen_clause (c, -flipped);
  } else return 0;

  return 1;
}

void Internal::subsume () {

  long check = 2*inc.subsume;

  inc.subsume += opts.subsumeinc;
  lim.subsume = stats.conflicts + inc.subsume;
  if (clauses.empty ()) return;

  START (subsume);

  size_t start = subsume_next;
  long tried = 0, subsumed = 0;
  int round = 0;

  while (tried < check) {
    if (subsume_next >= clauses.size ()) subsume_next = 0;
    if (subsume_next == start && round++) break;
    Clause * c = clauses[subsume_next++];
    const int tmp = subsume (c);
    if (tmp > 0) subsumed++;
    if (tmp) tried++;
  }

  VRB ("subsumed %ld ouf of %ld tried clauses %.2f",
    subsumed, tried, percent (subsumed, tried));

  report ('s');
  STOP (subsume);
}

};
