#include "clause.hpp"
#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "proof.hpp"
#include "macros.hpp"

#include <algorithm>

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// [PART 1] EAGER BACKWARD SUBSUMPTION

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
  LOG (c, "eagerly backward subsumed");
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
    LOG (c, "trying to eagerly backward subsume");
    if (eagerly_subsume_last_learned (c)) subsumed++;
    tried++;
  }
  unmark_clause ();
  LOG ("subsumed backward %d clauses out of %d tried", subsumed, tried);
  STOP (sublast);
}

/*------------------------------------------------------------------------*/

// [PART 2] GLOBAL FORWARD SUBSUMPTION IN PHASES

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
  if (subsuming->size == 2) stats.subchecks2++;
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

/*------------------------------------------------------------------------*/

// Candidate clause 'c' is strengthened by removing 'remove'.

inline void Internal::strengthen_clause (Clause * c, int remove) {
  assert (!watches ());
  stats.strengthened++;
  assert (c->size > 2);
  LOG (c, "removing %d in", remove);
  if (proof) proof->trace_strengthen_clause (c, remove);
  if (!c->redundant) mark_removed (remove);
  const const_literal_iterator end = c->end ();
  literal_iterator j = c->begin ();
  for (const_literal_iterator i = j; i != end; i++)
    if ((*j++ = *i) == remove) j--;
  assert (j + 1 == end);
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

inline int
Internal::try_to_subsume_clause (Clause * c, vector<Clause *> & shrunken) {

  stats.subtried++;
  assert (!level);
  LOG (c, "trying to subsume");

  mark (c);

  Clause * d = 0;
  int flipped = 0;
  const const_literal_iterator ec = c->end ();
  for (const_literal_iterator i = c->begin (); !d && i != ec; i++) {
    int lit = *i;
    if (!flags (lit).added) continue;
    for (int sign = -1; !d && sign <= 1; sign += 2) {
      Occs & os = occs (sign * lit);
      const const_occs_iterator eo = os.end ();
      occs_iterator k = os.begin ();
      for (const_occs_iterator j = k; j != eo; j++) {
        Clause * e = *j;
        if (e->garbage) continue;
        *k++ = e;
        if (d) continue;                        // need to copy rest
        flipped = subsume_check (e, c);
        if (!flipped) continue;
        d = e;                                  // leave outer loop
        if (flipped == INT_MIN) continue;
        if (sign < 0) assert (flipped == -lit), k--;
        else assert (flipped != lit);
      }
      os.resize (k - os.begin ());
      shrink_occs (os);
    }
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
    assert (likely_to_be_kept_clause (c));
    shrunken.push_back (c);
    return -1;
  }

  return 0;
}

/*------------------------------------------------------------------------*/

// Sorting the scheduled clauses is way faster if we compute and save the
// clause size in the schedule to avoid pointer access to clauses during
// sorting.  This slightly increases the schedule size though.

struct ClauseSize {
  int size;
  size_t cidx;
  ClauseSize (int s, size_t i) : size (s), cidx (i) { }
  ClauseSize () { }
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

struct less_noccs {
  Internal * internal;
  less_noccs (Internal * i) : internal (i) { }
  bool operator () (int a, int b) {
    int u = internal->val (a), v = internal->val (b);
    if (!u && v) return true;
    if (u && !v) return false;
    long m = internal->noccs (a), n = internal ->noccs (b);
    if (m < n) return true;
    if (m > n) return false;
    return abs (a) < abs (b);
  }
};

/*------------------------------------------------------------------------*/

// Usually called from 'subsume' below if 'subsuming' triggered it.  Then
// the idea is to subsume both redundant and irredundant clauses. It is also
// called in the elimination loop in 'elim' in which case we focus on
// irredundant clauses only to help bounded variable elimination.

void Internal::subsume_round () {

  if (!opts.subsume) return;

  SWITCH_AND_START (search, simplify, subsume);
  stats.subsumptions++;

  lim.added_at_last_subsume = stats.added;

  assert (!level);

  // Allocate schedule and occurrence lists.
  //
  vector<ClauseSize> schedule;
  init_noccs ();

  // Determine candidate clauses and sort them by size.
  //
  const size_t size = clauses.size ();
  for (size_t i = 0; i != size; i++) {
    Clause * c = clauses[i];
    if (c->garbage) continue;
    if (c->size > opts.subsumeclslim) continue;
    if (!likely_to_be_kept_clause (c)) continue;

    const const_literal_iterator end = c->end ();
    const_literal_iterator l;
    int lit = 0;

    bool fixed = false;
    int added = 0;
    for (l = c->begin (); !fixed && l != end; l++)
      if (val ((lit = *l))) fixed = true;
      else if (flags (lit).added) added++;

    // If the clause contains a root level assigned (fixed) literal we will
    // not work on it.  This simplifies the code substantially since we do
    // not have to care about assignments at all.  Strengthening becomes
    // much simpler too.  
    //
    if (fixed) {
      LOG (c, "skipping (fixed literal %d)", lit);
      continue;
    }

    // Further, if less than two  variables in the clause were added since
    // the last subsumption round, the clause is ignored too.
    //
    if (added < 2) {
      LOG (c, "skipping (only %d added literals)", added);
      continue;
    }

    schedule.push_back (ClauseSize (c->size, i));
    for (l = c->begin (); l != end; l++)
      noccs (*l)++;
  }
  shrink_vector (schedule);

  // Smaller clauses are checked and connected first.
  //
  sort (schedule.begin (), schedule.end (), smaller_clause_size ());

  // Drop 'opts.subsumeignore' fraction of variables.
  //
  size_t ignore = (1 - opts.subsumeignore) * schedule.size ();
  if (ignore < schedule.size ()) {
    int long limit = schedule[ignore].size;
    while (++ignore < schedule.size () && schedule[ignore].size == limit)
      ;
    schedule.resize (ignore);
    shrink_vector (schedule);
  }

  long scheduled = schedule.size ();
  long total = stats.irredundant + stats.redundant;
  VRB ("subsume", stats.subsumptions,
    "scheduled %ld clauses %.0f%% out of %ld clauses",
    scheduled, percent (scheduled, total), total);

  // Now go over the scheduled clauses in the order of increasing size and
  // try to forward subsume and strengthen them. Forward subsumptions tries
  // to find smaller or same size clauses which subsume or might strengthen
  // the candidate.  After the candidate has been processed connect one
  // of its literals (with smallest number of occurrences at this point) in
  // a one-watched scheme.

  long subsumed = 0, strengthened = 0;

  const const_clause_size_iterator eos = schedule.end ();
  const_clause_size_iterator s;

  vector<Clause *> shrunken;
  init_occs ();

  for (s = schedule.begin (); s != eos; s++) {

    Clause * c = clauses[s->cidx];
    assert (!c->garbage);

    // First try to subsume or strengthen this candidate clause.  For binary
    // clauses this could be done much faster by hashing and is costly due
    // to a usually large number of binary clauses.  There is further the
    // issue, that strengthening binary clauses (through double
    // self-subsuming resolution) would produce units, which needs much more
    // care. In the same (lazy) spirit we also ignore clauses with fixed
    // literals (false or true).
    //
    if (c->size > 2) {
      const int tmp = try_to_subsume_clause (c, shrunken);
      if (tmp > 0) { subsumed++; continue; }
      if (tmp < 0) strengthened++;
    }

    // If not subsumed connect smallest occurring literal, where occurring
    // means the number of times it was used to connect (as a one watch) a
    // previous smaller or equal sized clause.  This minimizes the length of
    // the occurrence lists traversed during 'try_to_subsume_clause'. Also
    // note that this number is usually way smaller than the number of
    // occurrences computed before and stored in 'noccs'.
    //
    int minlit = 0;
    long minoccs = 0;
    size_t minsize = 0;
    bool added = true;

    const const_literal_iterator end = c->end ();
    const_literal_iterator j;

    for (j = c->begin (); added && j != end; j++) {
      const int lit = *j;
      const size_t size = occs (lit).size ();
      if (!flags (lit).added) added = false;
      if (minlit && minsize <= size) continue;
      const long tmp = noccs (lit);
      if (minlit && minsize == size && tmp <= minoccs) continue;
      minlit = lit, minsize = size, minoccs = tmp;
    }

    // If there is a variable in the clause which is not 'added', then this
    // clause can not serve to strengthen or subsume another clause, since
    // all shrunken or added clauses mark all their variables as 'added'.
    //
    if (!added) continue;

    // If this smallest occurring literal occurs too often do not
    // connect the clause.
    //
    if (minsize > (size_t) opts.subsumeocclim) continue;

    LOG (c, "watching %d with %ld current and total %ld occurrences",
      minlit, (long) minsize, minoccs);
    occs (minlit).push_back (c);

    // This sorting should give faster failures for assumption checks since
    // the less occurring variables are put first in a clause and thus will
    // make it more likely to be found as witness for a clause not to be
    // subsuming.  One could in principle (see also the discussion on
    // 'subsumption' in the 'Splatz' solver) replace marking by a kind of
    // merge sort, which we do not want to do.  It would avoid 'marked'
    // calls and thus might be slightly faster.
    //
    sort (c->begin (), c->end (), less_noccs (this));
  }

  VRB ("subsume", stats.subsumptions,
    "subsumed %ld and strengthened %ld of %ld clauses %.0f%%",
    subsumed, strengthened, scheduled,
    percent (subsumed + strengthened, scheduled));

  // Release occurrence lists and schedule.
  //
  erase_vector (schedule);
  reset_noccs ();
  reset_occs ();

  // Reset all old 'added' flags and mark variables in shrunken
  // clauses as 'added' for the next subsumption round.
  //
  reset_added ();
  for (const_clause_iterator i = shrunken.begin ();
       i != shrunken.end ();
       i++)
    mark_added (*i);
  erase_vector (shrunken);

  lim.subsume = stats.conflicts + inc.subsume;

  report ('s');
  STOP_AND_SWITCH (subsume, simplify, search);
}

void Internal::subsume () {
  assert (opts.subsume);
  assert (!unsat);
  backtrack ();
  reset_watches ();
  subsume_round ();
  init_watches ();
  connect_watches ();
  inc.subsume += opts.subsumeinc;
  lim.subsume = stats.conflicts + inc.subsume;
}

};
