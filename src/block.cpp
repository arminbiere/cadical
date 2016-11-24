#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

#include <algorithm>

namespace CaDiCaL {

bool Internal::block_clause_on_literal (Clause * c, int pivot) {
  assert (!val (pivot));
  assert (!eliminated (pivot));
  LOG (c, "trying to block on %d", pivot);
  mark (c);
  assert (marked (pivot) > 0);
  Occs & os = occs (-pivot);
  const const_occs_iterator eos = os.end ();
  occs_iterator sos = os.begin (), i;
  for (i = sos; i != eos; i++) {
    Clause * d = *i;
    if (d->garbage) continue;
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

struct more_occs {
  Internal * internal;
  more_occs (Internal * i) : internal (i) { }
  bool operator () (int l, int k) const {
    long m = internal->occs (l).size ();
    long n = internal->occs (k).size ();
    if (m > n) return true;
    if (m < n) return false;
    int i = abs (k), j = abs (l);
    if (i > j) return true;
    if (i < j) return false;
    return l < k;
  }
};

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

  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx) || eliminated (idx)) continue;
    for (int sign = -1; sign <= 1; sign += 2) {
      const int lit = sign*idx;
      Occs & os = occs (lit);
      stable_sort (os.begin (), os.end (), smaller_size ());
    }
  }

  vector<int> schedule;
  char * scheduled;
  NEW (scheduled, char, 2*(max_var + 1));
  ZERO (scheduled, char, 2*(max_var + 1));
  scheduled += max_var;

  for (int idx = 1; idx <= max_var; idx++) {
    if (val (idx)) continue;
    if (eliminated (idx)) continue;
    if (!flags (idx).removed) continue;
    schedule.push_back (idx);
    schedule.push_back (-idx);
    scheduled[idx] = scheduled[-idx] = 1;
  }

  sort (schedule.begin (), schedule.end (), more_occs (internal));

  LOG ("scheduled %ld literals", (long) schedule.size ());

  while (!schedule.empty ()) {
    int lit = schedule.back ();
    schedule.pop_back ();
    assert (scheduled[lit]);
    scheduled[lit] = 0;
    Occs & os = occs (lit);
    LOG ("trying to block %ld clauses on %d", (long) os.size (), lit);
    const const_occs_iterator eor = os.end ();
    occs_iterator j = os.begin ();
    const_occs_iterator i;
    for (i = j; i != eor; i++) {
      Clause * c = *i;
      if (c->garbage) continue;
      if (block_clause_on_literal (c, lit)) {
	LOG (c, "blocked on %d", lit);
	push_on_extension_stack (c, lit);
	const const_literal_iterator eoc = c->end ();
	const_literal_iterator l;
	for (l = c->begin (); l != eoc; l++) {
	  const int other = *l;
	  if (val (other)) continue;
	  if (scheduled[-other]) continue;
	  scheduled[-other] = 1;
	  schedule.push_back (-other);
	}
	stats.blocked++;
	mark_garbage (c);
      } else *j++ = c;
    }
    os.resize (j - os.begin ());
  }

  scheduled -= max_var;
  DEL (scheduled, char, 2*(max_var + 1));
  erase_vector (schedule);
  reset_occs ();

  long blocked = stats.blocked - before;
  VRB ("block", stats.blockings,
    "blocked %ld clauses out of %.2f%% (%.0f%% remain)",
    blocked, percent (blocked, oldirr),
    percent (stats.irredundant, stats.original));
  report ('b');
  STOP (block);
}

};
