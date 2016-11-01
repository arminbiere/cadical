#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"
#include "profile.hpp"
#include "iterator.hpp"

#include <algorithm>

namespace CaDiCaL {

bool Internal::eliminating () {
  if (!opts.elim) return false;
  if (stats.conflicts != lim.conflicts_at_last_reduce) return false;
  return lim.elim <= stats.conflicts;
}

void Internal::elim (int lit) {
}

void Internal::elim () {

  SWITCH_AND_START (search, simplify, elim);
  stats.eliminations++;

  // Otherwise lots of contracts fail.
  //
  backtrack ();
  if (lim.fixed_at_last_collect < stats.fixed) garbage_collection ();

  // Allocate schedule and occurrence lists.
  //
  vector<int> schedule;
  init_occs ();

  // Connect all irredundant clauses.
  //
  const const_clause_iterator eoc = clauses.end ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != eoc; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (c->redundant) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != eol; j++) {
      int lit = *j;
      assert (!val (lit));
      occs[lit].push_back (c);
    }
  }
  account_occs ();

  // Now find elimination candidates.
  //
  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx)) continue;
    if (occs[idx].empty () && occs[-idx].empty ()) continue;
    schedule.push_back (idx);
  }
  inc_bytes (VECTOR_BYTES (schedule));
  VRB ("scheduled %ld variables for elimination",
    (long) schedule.size ());

  // And sort according to the number of occurrences.
  //
  stable_sort (schedule.begin (), schedule.end (), sum_occs_smaller (this));

  long old_resolutions = stats.resolutions;
  int old_eliminated = stats.eliminated;

  // Try eliminating variables according to the schedule.
  const const_int_iterator eos = schedule.end ();
  const_int_iterator k;
  for (k = schedule.begin (); k != eos; k++)
    elim (*k);					// TODO garbage collection!

  long resolutions = stats.resolutions - old_resolutions;
  int eliminated = stats.eliminated - old_eliminated;
  VRB ("eliminated %ld variables in %ld resolutions",
    eliminated, resolutions);

  // Release occurrence lists and schedule.
  //
  reset_occs ();
  dec_bytes (VECTOR_BYTES (schedule));
  schedule = vector<int> ();

  for (i = clauses.begin (); i != eoc; i++) {
    Clause * c = *i;
    if (c->garbage) continue;
    if (!c->redundant) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator j;
    for (j = c->begin (); j != eol; j++) {
      int lit = *j;
      if (this->eliminated (lit)) break;
    }
    if (j != eol) mark_garbage (c);
  }

  garbage_collection ();
  inc.elim *= 2;
  lim.elim = stats.conflicts + inc.elim;
  report ('e');
  STOP_AND_SWITCH (elim, simplify, search);
}

};
