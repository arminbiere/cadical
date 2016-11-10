#include "clause.hpp"
#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "proof.hpp"
#include "macros.hpp"

#include <algorithm>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// For certain instances it happens quite frequently that learned clauses
// backward subsume some of the recently learned clauses.  Thus whenever we
// learn a clause, we can eagerly check whether one of the last
// 'opts.sublast' learned clauses is subsumed by the new learned clause.
//
// This observation and the idea for this code is due to Donald Knuth (even
// though he originally only tried to subsume the very last clause).  Note
// that 'backward' means the learned clause from which we start the
// subsumption check is checked for subsuming earlier (larger) clauses.

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
  mark_garbage (c);
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

// The rest of the file implements a global forward subsumption algorithm,
// which is run frequently during search.  It works both on original
// (irredundant) clauses and on 'sticky' learned clauses which are small
// enough or have a small enough glue to be otherwise kept forever (see
// 'opts.keepsize' and 'opts.keeglue', e.g., a redundant clause is not
// extended and thus kept if its size is smaller equal to 'opts.keepsize' or
// its glue is smaller equal than 'opts.keepsize').  Note, that 'forward'
// means that the clause from which the subsumption check is started is
// checked for being subsumed by other (smaller or equal size) clauses.

bool Internal::subsuming () {

  if (!opts.subsume) return false;

  // Only perform global subsumption checking immediately after a clause
  // reduction happened where the overall allocated memory is small and we
  // got a limit on the number of kept clause in terms of size and glue.
  //
  if (opts.reduce &&
      stats.conflicts != lim.conflicts_at_last_reduce) return false;

  return stats.conflicts >= lim.subsume;
}

// This is the actual subsumption and strengthening check.  We assume that
// all the literals of the candidate clause to be subsumed or strengthened
// are marked, so we only have to check that all the literals of the
// argument clause 'subsuming', which is checked for subsuming the candidate
// clause 'subsumed', has all its literals marked (in the correct phase).
// If exactly one is in the opposite phase we can still strengthen the
// candidate clause by this single literal which occurs in opposite phase.
//
// The result is INT_MIN if all literals are marked and thus the candidate
// clause can be subsumed.  It is zero if neither subsumption nor
// strengthening is possible.  Otherwise the candidate clause can be
// strengthened and as a result the negation of the literal which can be
// removed is returned.

inline int Internal::subsume_check (Clause * subsuming,
                                    Clause * subsumed) {

  // Only use 'subsumed' for these following assertion checks.  Otherwise we
  // only require that 'subsumed' has all its literals marked.
  //
  assert (!subsumed->garbage);
  assert (!subsuming->garbage);
  assert (subsuming != subsumed);
  assert (subsuming->size <= subsumed->size);

  stats.subchecks++;
  const const_literal_iterator end = subsuming->end ();
  int flipped = 0;
  for (const_literal_iterator i = subsuming->begin (); i != end; i++) {
    const int lit = *i, tmp = marked (lit);
    if (!tmp) return 0;
    if (tmp > 0) continue;
    if (flipped) return 0;
    flipped = lit;
  }
  if (!flipped) return INT_MIN;                   // subsumed!!
  else if (!opts.strengthen) return 0;
  else return flipped;                            // strengthen!!
}

/*------------------------------------------------------------------------*/

// Candidate clause 'subsumed' is subsumed by 'subsuming'.

inline void
Internal::subsume_clause (Clause * subsuming, Clause * subsumed) {
  stats.subsumed++;
  assert (subsuming->size <= subsumed->size);
  LOG (subsumed, "subsumed");
  if (subsumed->redundant) stats.subred++; else stats.subirr++;
  mark_garbage (subsumed);
  if (subsumed->redundant || !subsuming->redundant) return;
  LOG ("turning redundant subsuming clause into irredundant clause");
  subsuming->redundant = false;
  stats.irredundant++;
  assert (stats.redundant);
  stats.redundant--;
}

// Candidate clause 'c' is strengthened by removing 'remove'.

inline void Internal::strengthen_clause (Clause * c, int remove) {
#if 0
  if (watches ()) {
    // An alternative is to remove and update watch lists, which is pretty
    // expensive (quadratic in accumulated in the worst case).  Thus we just
    // skip strengthening this clause if the removed literal is watched.
    if (c->literals[0] == remove ||
        c->literals[1] == remove) return;
  }
#else
  assert (!watches ());
#endif
  stats.strengthened++;
  assert (c->size > 2);
  LOG (c, "removing %d in", remove);
  if (proof) proof->trace_strengthen_clause (c, remove);
  if (!c->redundant) touch_clause (c);
  const const_literal_iterator end = c->end ();
  literal_iterator j = c->begin ();
  for (const_literal_iterator i = j; i != end; i++)
    if ((*j++ = *i) == remove) j--;
  assert (j + 1 == end);
  dec_bytes (sizeof (int));;
  c->size--;
  if (c->pos > c->size) c->pos = 2;
  if (c->redundant && c->glue > c->size) c->glue = c->size;
  if (c->extended) c->analyzed () = ++stats.analyzed;
  LOG (c, "strengthened");
  check_shrunken_clause (c);
}

/*------------------------------------------------------------------------*/

// Find clauses connected in the occurrence lists 'occs' which subsume the
// candidate clause 'c' given as first argument.  If this is the case the
// clause is subsumed and the result is positive.   If the clause was
// strengthened the result is negative.  Otherwise the candidate clause
// can not be subsumed nor strengthened and zero is returned.

inline int Internal::try_to_subsume_clause (Clause * c,
                                            bool irredundant_only,
					    long old_touched) {

  stats.subtried++;
  assert (!level);
  LOG (c, "trying to subsume");

  mark (c);

  Clause * d = 0;
  int flipped = 0;
  const const_literal_iterator ec = c->end ();
  for (const_literal_iterator i = c->begin (); !d && i != ec; i++) {
    int lit = *i;
    if (irredundant_only &&
        touched (lit) <= old_touched &&
        touched (-lit) <= old_touched)
      continue;
    Occs & os = occs (lit);
    const const_clause_iterator eo = os.end ();
    clause_iterator k = os.begin ();
    for (const_clause_iterator j = k; j != eo; j++) {
      Clause * e = *j;
      if (e->garbage) continue;
      *k++ = e;
      if (d) continue;
      flipped = subsume_check (e, c);
      if (flipped) d = e;                 // ... and leave outer loop.
    }
    os.resize (k - os.begin ());
    shrink_vector (os);
  }

  unmark (c);

  if (flipped == INT_MIN) {
    LOG (d, "subsuming");
    subsume_clause (d, c);
    return 1;
  }

  if (flipped) {
    LOG (d, "strengthening");
    strengthen_clause (c, -flipped);
    return -1;
  }

  return 0;
}

/*------------------------------------------------------------------------*/

// Sorting the scheduled clauses is way faster if we compute save the clause
// size in the schedule to avoid pointer access to clauses during sorting.
// This slightly increases the schedule size though.

struct ClauseSize {
  int size;
  size_t cidx;
  ClauseSize (int s, size_t i) : size (s), cidx (i) { }
};

typedef vector<ClauseSize>::const_iterator const_clause_size_iterator;
typedef vector<ClauseSize>::iterator clause_size_iterator;

struct smaller_clause_size {
  bool operator () (const ClauseSize & a, const ClauseSize & b) const {
    if (a.size < b.size) return true;
    if (a.size > b.size) return false;
    return a.cidx < b.cidx;
  }
};

/*------------------------------------------------------------------------*/

// Usually called from 'subsume' below if 'subsuming' triggered it.  Then
// the idea is to subsume both redundant and irredundant clauses. It is also
// called in the elimination loop in 'elim' in which case we focus on
// irredundant clauses only to help bounded variable elimination.

bool Internal::subsume_round (bool irredundant_only) {

  if (!opts.subsume) return false;

  SWITCH_AND_START (search, simplify, subsume);
  stats.subsumptions++;

  long old_touched = lim.touched_at_last_subsume;
  lim.touched_at_last_subsume = stats.touched;

  assert (!level);

  // Allocate schedule and occurrence lists.
  //
  vector<ClauseSize> schedule;
  init_occs ();

  // Determine candidate clauses and sort them by size.
  //
  const size_t size = clauses.size ();
  for (size_t i = 0; i != size; i++) {
    Clause * c = clauses[i];
    if (c->garbage) continue;
    if (clause_contains_fixed_literal (c)) continue;
    if (c->redundant) {
      if (irredundant_only) continue;
      if (c->extended) {
        // All irredundant clauses and short clauses with small glue (not
        // extended) are candidates in any case.  Otherwise, redundant long
        // clauses are considered as candidates if they would have been kept
        // in the last 'reduce' operation based on their size and glue value.
        if (c->size > lim.keptsize || c->glue > lim.keptglue) continue;
      }
    } else if (irredundant_only) {
      const const_literal_iterator end = c->end ();
      const_literal_iterator l;
      for (l = c->begin (); l != end; l++) {
	const int lit = *l;
	if (touched (lit) > old_touched  ||
	    touched (-lit) > old_touched) break;
      }
      if (l == end) continue;
    }
    schedule.push_back (ClauseSize (c->size, i));
  }
  shrink_vector (schedule);
  inc_bytes (bytes_vector (schedule));

  sort (schedule.begin (), schedule.end (), smaller_clause_size ());

  long scheduled = schedule.size ();
  long total = stats.irredundant;
  if (!irredundant_only) total += stats.redundant;
  VRB ("subsume", stats.subsumptions,
    "scheduled %ld clauses %.0f%% of all %ld %sclauses",
    scheduled, percent (scheduled, total), total,
    (irredundant_only ? "irredundant " : ""));

  // Now go over the scheduled clauses in the order of increasing size and
  // try to forward subsume and strengthen them. Forward means find smaller
  // or same size clauses which subsume or might strengthen the candidate.
  // After the candidate has been processed connect its literals.

  long subsumed = 0, strengthened = 0;

  const const_clause_size_iterator eos = schedule.end ();
  const_clause_size_iterator s;
  for (s = schedule.begin (); s != eos; s++) {

    Clause * c = clauses[s->cidx];
    assert (!c->garbage);

    // First try to subsume or strengthen this candidate clause.  For binary
    // clauses this could be done much faster by hashing and is costly due
    // to large number of binary clauses.  There is further the issue, that
    // strengthening binary clauses (through double self-subsuming
    // resolution) would produce units, which needs much more care. For now
    // we ignore clauses with fixed literals (false or true).
    //
    if (c->size > 2) {
      const int tmp =
        try_to_subsume_clause (c, irredundant_only, old_touched);
      if (tmp > 0) { subsumed++; continue; }
      if (tmp < 0) strengthened++;
    }

    // If not subsumed connect smallest occurring literal.
    //
    int minlit = 0;
    size_t minsize = 0;
    const const_literal_iterator end = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != end; j++) {
      const int lit = *j;
      const size_t size = occs (lit).size ();
      if (minlit && minsize <= size) continue;
      minlit = lit, minsize = size;
    }

    // Unless this smallest occurring literal occurs too often.
    // Ignore potential subsumed garbage clauses.
    //
    if (minsize > (size_t) opts.subsumeocclim) continue;

    LOG (c, "watching %d with %ld occurrences", minlit, (long) minsize);
    occs (minlit).push_back (c);
  }

  // Release occurrence lists and schedule and reconnected watches.
  //
  dec_bytes (bytes_vector (schedule));
  erase_vector (schedule);
  reset_occs ();

  VRB ("subsume", stats.subsumptions,
    "subsumed %ld and strengthened %ld of %ld clauses %.0f%%",
    subsumed, strengthened, scheduled,
    percent (subsumed + strengthened, scheduled));

  lim.subsume = stats.conflicts + inc.subsume;

  report ('s');
  STOP_AND_SWITCH (subsume, simplify, search);

  return subsumed > 0;
}

void Internal::subsume () {
  assert (opts.subsume);
  assert (!unsat);
  backtrack ();
  reset_watches ();
  (void) subsume_round (false);
  init_watches ();
  connect_watches ();
  inc.subsume += opts.subsumeinc;
  lim.subsume = stats.conflicts + inc.subsume;
}

};
