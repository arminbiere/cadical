#include "internal.hpp"

namespace CaDiCaL {

External::External (Internal * i)
:
  internal (i),
  max_var (0),
  vsize (0),
  extended (false),
  terminator (0),
  learner (0),
  solution (0),
  vars (max_var)
{
  assert (internal);
  assert (!internal->external);
  internal->external = this;
}

External::~External () {
  if (solution) delete [] solution;
}

void External::enlarge (int new_max_var) {

  assert (!extended);

  size_t new_vsize = vsize ? 2*vsize : 1 + (size_t) new_max_var;
  while (new_vsize <= (size_t) new_max_var) new_vsize *= 2;
  LOG ("enlarge external size from %zd to new size %zd", vsize, new_vsize);
  vsize = new_vsize;
}

void External::init (int new_max_var) {
  assert (!extended);
  if (new_max_var <= max_var) return;
  int new_vars = new_max_var - max_var;
  int old_internal_max_var = internal->max_var;
  int new_internal_max_var = old_internal_max_var + new_vars;
  internal->init_vars (new_internal_max_var);
  if ((size_t) new_max_var >= vsize) enlarge (new_max_var);
  LOG ("initialized %d external variables", new_vars);
  if (!max_var) {
    assert (e2i.empty ());
    e2i.push_back (0);
    assert (internal->i2e.empty ());
    internal->i2e.push_back (0);
  } else {
    assert (e2i.size () == (size_t) max_var + 1);
    assert (internal->i2e.size () == (size_t) old_internal_max_var + 1);
  }
  unsigned iidx = old_internal_max_var + 1, eidx;
  for (eidx = max_var + 1u;
       eidx <= (unsigned) new_max_var;
       eidx++, iidx++) {
    LOG ("mapping external %u to internal %u", eidx, iidx);
    assert (e2i.size () == eidx);
    e2i.push_back (iidx);
    internal->i2e.push_back (eidx);
    assert (internal->i2e[iidx] == (int) eidx);
    assert (e2i[eidx] == (int) iidx);
  }
  if (internal->opts.checkfrozen)
    while (new_max_var >= (int64_t) moltentab.size ())
      moltentab.push_back (false);
  assert (iidx == (size_t) new_internal_max_var + 1);
  assert (eidx == (size_t) new_max_var + 1);
  max_var = new_max_var;
}

/*------------------------------------------------------------------------*/

void External::reset_assumptions () {
  assumptions.clear ();
  internal->reset_assumptions ();
}

void External::reset_extended () {
  if (!extended) return;
  LOG ("reset extended");
  extended = false;
}

void External::reset_limits () {
  internal->reset_limits ();
}

/*------------------------------------------------------------------------*/

int External::internalize (int elit) {
  int ilit;
  if (elit) {
    assert (elit != INT_MIN);
    const int eidx = abs (elit);
    if (eidx > max_var) init (eidx);
    ilit = e2i [eidx];
    if (elit < 0) ilit = -ilit;
    if (!ilit) {
      assert (internal->max_var < INT_MAX);
      ilit = internal->max_var + 1u;
      internal->init_vars (ilit);
      e2i[eidx] = ilit;
      LOG ("mapping external %d to internal %d", eidx, ilit);
      e2i[eidx] = ilit;
      internal->i2e.push_back (eidx);
      assert (internal->i2e[ilit] == eidx);
      assert (e2i[eidx] == ilit);
      if (elit < 0) ilit = -ilit;
    }
    if (internal->opts.checkfrozen) {
      assert (eidx < (int64_t) moltentab.size ());
      if (moltentab[eidx])
        FATAL ("can not reuse molten literal %d", eidx);
    }
    Flags & f = internal->flags (ilit);
    if (f.status == Flags::UNUSED) internal->mark_active (ilit);
    else if (f.status != Flags::ACTIVE &&
             f.status != Flags::FIXED) internal->reactivate (ilit);
    if (!marked (tainted, elit) && marked (witness, -elit)) {
      assert (!internal->opts.checkfrozen);
      LOG ("marking tainted %d", elit);
      mark (tainted, elit);
    }
  } else ilit = 0;
  return ilit;
}

void External::add (int elit) {
  assert (elit != INT_MIN);
  reset_extended ();
  if (internal->opts.check &&
      (internal->opts.checkwitness || internal->opts.checkfailed))
    original.push_back (elit);
  const int ilit = internalize (elit);
  assert (!elit == !ilit);
  if (elit) LOG ("adding external %d as internal %d", elit, ilit);
  internal->add_original_lit (ilit);
}

void External::assume (int elit) {
  assert (elit);
  reset_extended ();
  assumptions.push_back (elit);
  const int ilit = internalize (elit);
  assert (ilit);
  LOG ("assuming external %d as internal %d", elit, ilit);
  internal->assume (ilit);
}

bool External::failed (int elit) {
  assert (elit);
  assert (elit != INT_MIN);
  int eidx = abs (elit);
  if (eidx > max_var) return 0;
  int ilit = e2i[eidx];
  if (!ilit) return 0;
  if (elit < 0) ilit = -ilit;
  return internal->failed (ilit);
}

void External::phase (int elit) {
  assert (elit);
  assert (elit != INT_MIN);
  int eidx = abs (elit);
  if (eidx > max_var) return;
  int ilit = e2i[eidx];
  if (!ilit) return;
  if (elit < 0) ilit = -ilit;
  internal->phase (ilit);
}

void External::unphase (int elit) {
  assert (elit);
  assert (elit != INT_MIN);
  int eidx = abs (elit);
  if (eidx > max_var) return;
  int ilit = e2i[eidx];
  if (!ilit) return;
  if (elit < 0) ilit = -ilit;
  internal->unphase (ilit);
}

/*------------------------------------------------------------------------*/

// Internal checker if 'solve' claims the formula to be satisfiable.

void External::check_satisfiable () {
  LOG ("checking satisfiable");
  if (internal->opts.checkwitness)
    check_assignment (&External::ival);
  if (internal->opts.checkassumptions && !assumptions.empty ())
    check_assumptions_satisfied ();
}

// Internal checker if 'solve' claims formula to be unsatisfiable.

void External::check_unsatisfiable () {
  LOG ("checking unsatisfiable");
  if (internal->opts.checkfailed && !assumptions.empty ())
    check_assumptions_failing ();
}

// Check result of 'solve' to be correct.

void External::check_solve_result (int res) {
  if (!internal->opts.check) return;
  if (res == 10) check_satisfiable ();
  if (res == 20) check_unsatisfiable ();
}

// Prepare checking that completely molten literals are not used as argument
// of 'add' or 'assume', which is invalid under freezing semantics.  This
// case would be caught by our 'restore' implementation so is only needed
// for checking the deprecated 'freeze' semantics.

void External::update_molten_literals () {
  if (!internal->opts.checkfrozen) return;
  assert ((size_t) max_var + 1 == moltentab.size ());
  int registered = 0, molten = 0;
  for (auto lit : vars) {
    if (moltentab[lit]) {
      LOG ("skipping already molten literal %d", lit);
      molten++;
    } else if (frozen (lit))
      LOG ("skipping currently frozen literal %d", lit);
    else {
      LOG ("new molten literal %d", lit);
      moltentab[lit] = true;
      registered++;
      molten++;
    }
  }
  LOG ("registered %d new molten literals", registered);
  LOG ("reached in total %d molten literals", molten);
}

int External::solve (bool preprocess_only) {
  reset_extended ();
  update_molten_literals ();
  int res = internal->solve (preprocess_only);
  if (res == 10) extend ();
  check_solve_result (res);
  reset_limits ();
  return res;
}

void External::terminate () { internal->terminate (); }

int External::lookahead () {
  reset_extended ();
  update_molten_literals ();
  int ilit = internal->lookahead ();
  const int elit = (ilit && ilit != INT_MIN) ? internal->externalize (ilit) : 0;
  LOG ("lookahead internal %d external %d", ilit, elit);
  return elit;
}

CaDiCaL::CubesWithStatus External::generate_cubes (int depth) {
  reset_extended ();
  update_molten_literals ();
  reset_limits ();
  auto cubes = internal->generate_cubes (depth);
  auto externalize = [this](int ilit) {
    const int elit = ilit ? internal->externalize (ilit) : 0;
    MSG ("lookahead internal %d external %d", ilit, elit);
    return elit;
  };
  auto externalize_map = [this, externalize](std::vector<int> cube) {
    (void) this;
    MSG("Cube : ");
    std::for_each(begin(cube), end(cube), externalize);
  };
    std::for_each(begin(cubes.cubes), end(cubes.cubes), externalize_map);

    return cubes;
}

/*------------------------------------------------------------------------*/

void External::freeze (int elit) {
  reset_extended ();
  int ilit = internalize (elit);
  unsigned eidx = vidx (elit);
  while (eidx >= frozentab.size ())
    frozentab.push_back (0);
  unsigned & ref = frozentab[eidx];
  if (ref < UINT_MAX) {
    ref++;
    LOG ("external variable %d frozen once and now frozen %u times",
      eidx, ref);
  } else
    LOG ("external variable %d frozen but remains frozen forever", eidx);
  internal->freeze (ilit);
}

void External::melt (int elit) {
  reset_extended ();
  int ilit = internalize (elit);
  unsigned eidx = vidx (elit);
  assert (eidx < frozentab.size ());
  unsigned & ref = frozentab[eidx];
  assert (ref > 0);
  if (ref < UINT_MAX) {
    if (!--ref)
      LOG ("external variable %d melted once and now completely melted",
        eidx);
    else
      LOG ("external variable %d melted once but remains frozen %u times",
        eidx, ref);
  } else
    LOG ("external variable %d melted but remains frozen forever", eidx);
  internal->melt (ilit);
}

/*------------------------------------------------------------------------*/

void External::check_assignment (int (External::*a)(int) const) {

  // First check all assigned and consistent.
  //
  for (auto idx : vars) {
    if (!(this->*a) (idx)) FATAL ("unassigned variable: %d", idx);
    if ((this->*a) (idx) != -(this->*a)(-idx))
      FATAL ("inconsistently assigned literals %d and %d", idx, -idx);
  }

  // Then check that all (saved) original clauses are satisfied.
  //
  bool satisfied = false;
  const auto end = original.end ();
  auto start = original.begin (), i = start;
  int64_t count = 0;
  for (; i != end; i++) {
    int lit = *i;
    if (!lit) {
      if (!satisfied) {
        fatal_message_start ();
        fputs ("unsatisfied clause:\n", stderr);
        for (auto j = start; j != i; j++)
          fprintf (stderr, "%d ", *j);
        fputc ('0', stderr);
        fatal_message_end ();
      }
      satisfied = false;
      start = i + 1;
      count++;
    } else if (!satisfied && (this->*a) (lit) > 0) satisfied = true;
  }
  VERBOSE (1,
    "satisfying assignment checked on %" PRId64 " clauses",
    count);
}

/*------------------------------------------------------------------------*/

void External::check_assumptions_satisfied () {
  for (const auto & lit : assumptions) {
    // Not 'signed char' !!!!
    const int tmp = ival (lit);
    if (tmp < 0) FATAL ("assumption %d falsified", lit);
    if (!tmp) FATAL ("assumption %d unassigned", lit);
  }
  VERBOSE (1,
    "checked that %zd assumptions are satisfied",
    assumptions.size ());
}

void External::check_assumptions_failing () {
  Solver * checker = new Solver ();
  checker->prefix ("checker ");
#ifdef LOGGING
  if (internal->opts.log) checker->set ("log", true);
#endif
  for (const auto & lit : original)
    checker->add (lit);
  for (const auto & lit : assumptions) {
    if (!failed (lit)) continue;
    LOG ("checking failed literal %d in core", lit);
    checker->add (lit);
    checker->add (0);
  }
  int res = checker->solve ();
  if (res != 20) FATAL ("failed assumptions do not form a core");
  delete checker;
  VERBOSE (1,
    "checked that %zd failing assumptions form a core",
    assumptions.size ());
}

/*------------------------------------------------------------------------*/

// Traversal of unit clauses is implemented here.

// In principle we want to traverse the clauses of the simplified formula
// only, particularly eliminated variables should be completely removed.
// This poses the question what to do with unit clauses.  Should they be
// considered part of the simplified formula or of the witness to construct
// solutions for the original formula?  Ideally they should be considered
// to be part of the witness only, i.e., as they have been simplified away.

// Therefore we distinguish frozen and non-frozen units during clause
// traversal.  Frozen units are treated as unit clauses while non-frozen
// units are treated as if they were already eliminated and put on the
// extension stack as witness clauses.

// Furthermore, eliminating units during 'compact' could be interpreted as
// variable elimination, i.e., just add the resolvents (remove falsified
// literals), then drop the clauses with the unit, and push the unit on the
// extension stack.  This is of course only OK if the user did not freeze
// that variable (even implicitly during assumptions).

// Thanks go to Fahiem Bacchus for asking why there is a necessity to
// distinguish these two cases (frozen and non-frozen units).  The answer is
// that it is not strictly necessary, and this distinction could be avoided
// by always treating units as remaining unit clauses, thus only using the
// first of the two following functions and dropping the 'if (!frozen (idx))
// continue;' check in it.  This has however the down-side that those units
// are still in the simplified formula and only as units.  I would not
// consider such a formula as really being 'simplified'. On the other hand
// if the user explicitly freezes a literal, then it should continue to be in
// the simplified formula during traversal.  So also only using the second
// function is not ideal.

// There is however a catch where this solution breaks down (in the sense of
// producing less optimal results - that is keeping units in the formula
// which better would be witness clauses).  The problem is with compact
// preprocessing which removes eliminated but also fixed internal variables.
// One internal unit (fixed) variable is kept and all the other external
// literals which became unit are mapped to that internal literal (negated
// or positively).  Compact is called non-deterministically from the point
// of the user and thus there is no control on when this happens.  If
// compact happens those external units are mapped to a single internal
// literal now and then all share the same 'frozen' counter.   So if the
// user freezes one of them all in essence get frozen, which in turn then
// makes a difference in terms of traversing such a unit as unit clause or
// as unit witness.

bool
External::traverse_all_frozen_units_as_clauses (ClauseIterator & it)
{
  if (internal->unsat) return true;

  vector<int> clause;

  for (auto idx : vars) {
    if (!frozen (idx)) continue;
    const int tmp = fixed (idx);
    if (!tmp) continue;
    int unit = tmp < 0 ? -idx : idx;
    clause.push_back (unit);
    if (!it.clause (clause))
      return false;
    clause.clear ();
  }

  return true;
}

bool
External::traverse_all_non_frozen_units_as_witnesses (WitnessIterator & it)
{
  if (internal->unsat) return true;

  vector<int> clause_and_witness;

  for (auto idx : vars) {
    if (frozen (idx)) continue;
    const int tmp = fixed (idx);
    if (!tmp) continue;
    int unit = tmp < 0 ? -idx : idx;
    clause_and_witness.push_back (unit);
    if (!it.witness (clause_and_witness, clause_and_witness))
      return false;
    clause_and_witness.clear ();
  }

  return true;
}

/*------------------------------------------------------------------------*/

void External::copy_flags (External & other) const {
  const vector<Flags> & this_ftab = internal->ftab;
  vector<Flags> & other_ftab = other.internal->ftab;
  const unsigned limit = min (max_var, other.max_var);
  for (unsigned eidx = 1; eidx <= limit; eidx++) {
    const int this_ilit = e2i[eidx];
    if (!this_ilit) continue;
    const int other_ilit = other.e2i[eidx];
    if (!other_ilit) continue;
    if (!internal->active (this_ilit)) continue;
    if (!other.internal->active (other_ilit)) continue;
    assert (this_ilit != INT_MIN);
    assert (other_ilit != INT_MIN);
    const Flags & this_flags = this_ftab[abs (this_ilit)];
    Flags & other_flags = other_ftab[abs (other_ilit)];
    this_flags.copy (other_flags);
  }
}

/*------------------------------------------------------------------------*/

void External::export_learned_empty_clause () {
  assert (learner);
  if (learner->learning (0)) {
    LOG ("exporting learned empty clause");
    learner->learn (0);
  } else
    LOG ("not exporting learned empty clause");
}

void External::export_learned_unit_clause (int ilit) {
  assert (learner);
  if (learner->learning (1)) {
    LOG ("exporting learned unit clause");
    const int elit = internal->externalize (ilit);
    assert (elit);
    learner->learn (elit);
    learner->learn (0);
  } else
    LOG ("not exporting learned unit clause");
}

void External::export_learned_large_clause (const vector<int> & clause) {
  assert (learner);
  size_t size = clause.size ();
  assert (size <= (unsigned) INT_MAX);
  if (learner->learning ((int) size)) {
    LOG ("exporting learned clause of size %zu", size);
    for (auto ilit : clause) {
      const int elit = internal->externalize (ilit);
      assert (elit);
      learner->learn (elit);
    }
    learner->learn (0);
  } else
    LOG ("not exporting learned clause of size %zu", size);
}

}
