#ifdef BCE

#include "heap.hpp"
#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

#include <algorithm>

namespace CaDiCaL {

bool Internal::block_clause_on_literal (Clause * c, int pivot) {
  assert (!val (pivot));
  assert (!flags (pivot).eliminated);
  Occs & os = occs (-pivot);
  LOG (c, "trying to block on %d where %d occurs %ld times",
    pivot, -pivot, (long) os.size ());
  if (os.empty ()) {
    LOG ("no occurrences of %d", -pivot);
    return true;
  }
  stats.blocktried++;
  mark (c);
  assert (marked (pivot) > 0);
  const const_occs_iterator eos = os.end ();
  occs_iterator sos = os.begin (), i;
  for (i = sos; i != eos; i++) {
    Clause * d = *i;
    if (d->redundant || d->garbage) continue;
    stats.blockres++;
    if (c->size == 2 || d->size == 2) stats.blockres2++;
    const const_literal_iterator eoc = d->end ();
    const_literal_iterator l;
    bool satisfied = false;
    for (l = d->begin (); !satisfied && l != eoc; l++) {
      const int lit = *l;
      if (lit == -pivot) continue;
      const int tmp = val (lit);
      if (tmp > 0) satisfied = true;
      else if (tmp < 0) continue;
      else if (marked (lit) < 0) {
	LOG (d, "clashing literal %d", lit);
	break;
      }
    }
    if (satisfied) mark_garbage (d);
    else if (l == eoc) {
      LOG (d, "non-tautological resolution candidate on %d", pivot);
      break;
    }
  }
  unmark (c);
  if (i == eos) return true;
  if (i != sos) {
    occs_iterator j;
    Clause * last = *i;
    for (j = sos; j != i; j++) swap (last, *j);
    *i = last;
  }
  return false;
}

struct more_negated_occs {
  Internal * internal;
  more_negated_occs (Internal * i) : internal (i) { }
  bool operator () (int l, int k) const {
    long m = internal->occs (-l).size ();
    long n = internal->occs (-k).size ();
    if (m > n) return true;
    if (m < n) return false;
    int i = abs (l), j = abs (k);
    if (i > j) return true;
    if (i < j) return false;
    return l > k;
  }
};

void Internal::turn_into_redundant_blocked_clause (Clause * c) {
  assert (!c->garbage);
  assert (!c->redundant);
  assert (stats.irredundant > 0);
  assert (stats.irrbytes >= (long) c->bytes ()), 
  stats.irredundant--;
  stats.irrbytes -= c->bytes ();
  mark_removed (c);
  c->redundant = 1;
  stats.redundant++;
  c->blocked = 1;
  stats.redblocked++;
  c->glue = c->size;
} 

void Internal::block () {

  assert (!level);
  assert (!watches ());

  if (!opts.block) return;

  START (block);
  stats.blockings++;

  LOG ("starting blocked clause elimination on %ld clauses",
    stats.irredundant);

  long before = stats.blocked, oldirr = stats.irredundant;

  init_occs ();
  const_clause_iterator i;
  for (i = clauses.begin (); i != clauses.end (); i++) {
    Clause * c = *i;
    if (c->redundant || c->garbage) continue;
    const const_literal_iterator eol = c->end ();
    const_literal_iterator l;
    bool satisfied = false;
    for (l = c->begin (); !satisfied && l != eol; l++) {
      const int lit = *l, tmp = val (lit);
      if (tmp > 0) satisfied = true;
      else if (!tmp) occs (lit).push_back (c);
    }
    if (satisfied) mark_garbage (c);
  }

  more_negated_occs less (this);
  heap<more_negated_occs> schedule = heap<more_negated_occs> (less);

  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx)) continue;
    if (flags (idx).eliminated) continue;
    if (stats.blockings > 1 && !flags (idx).removed) continue;
    schedule.push_back (idx);
    schedule.push_back (-idx);
  }

  LOG ("scheduled %ld literals", (long) schedule.size ());

  long delta = opts.blockreleff * stats.propagations;
  if (delta < opts.blockmineff) delta = opts.blockmineff;
  long limit = stats.blockres + delta;

  while (!schedule.empty () && stats.blockres < limit) {
    int lit = schedule.front ();
    schedule.pop_front ();
    Occs & os = occs (lit);
    LOG ("trying to block %ld clauses on %d", (long) os.size (), lit);
    const const_occs_iterator eor = os.end ();
    occs_iterator j = os.begin ();
    const_occs_iterator i;
    for (i = j; i != eor; i++) {
      Clause * c = *i;
      if (c->redundant || c->garbage) continue;
      if (block_clause_on_literal (c, lit)) {
	LOG (c, "blocked on %d", lit);
	push_on_extension_stack (c, lit);
	const const_literal_iterator eoc = c->end ();
	const_literal_iterator l;
	for (l = c->begin (); l != eoc; l++) {
	  const int other = *l;
	  if (val (other)) continue;
	  if (!schedule.contains (-other)) schedule.push_back (-other);
	}
	stats.blocked++;
	if (c->size > opts.blockeepsize) mark_garbage (c);
	else turn_into_redundant_blocked_clause (c);
      } else *j++ = c;
    }
    if (j == eor) continue;
    os.resize (j - os.begin ());
    if (schedule.contains (-lit)) schedule.update (-lit);
  }

  schedule.erase ();
  reset_occs ();

  long blocked = stats.blocked - before;
  VRB ("block", stats.blockings,
    "blocked %ld clauses %.2f%% of %ld (%.0f%% remain)",
    blocked, percent (blocked, oldirr), oldirr,
    percent (stats.irredundant, stats.original));
  report ('b');
  STOP (block);
}

};

#endif
