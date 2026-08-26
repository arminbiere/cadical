#include "internal.hpp"
#include "profile.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

inline unsigned Checker::l2u (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  unsigned res = 2 * (abs (lit) - 1);
  if (lit < 0)
    res++;
  return res;
}

inline signed char Checker::val (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  assert (abs (lit) < size_vars);
  assert (vals[lit] == -vals[-lit]);
  return vals[lit];
}

signed char &Checker::mark (int lit) {
  const unsigned u = l2u (lit);
  assert (u < marks.size ());
  return marks[u];
}

inline CheckerWatcher &Checker::watcher (int lit) {
  const unsigned u = l2u (lit);
  assert (u < watchers.size ());
  return watchers[u];
}

/*------------------------------------------------------------------------*/

CheckerClause *Checker::new_clause () {
  const size_t size = simplified.size ();
  // assert (size > 1);
  assert (size <= UINT_MAX);

  const size_t header_bytes = sizeof (CheckerClause);
  const size_t actual_literal_bytes = size * sizeof (int);
  size_t combined_bytes = header_bytes + actual_literal_bytes;
#ifdef NFLEXIBLE
  const size_t faked_literals_bytes =
      sizeof ((CheckerClause *) 0)->literals;
  combined_bytes -= faked_literals_bytes;
#endif
  CheckerClause *res = (CheckerClause *) new char[combined_bytes];
  DeferDeleteArray<char> delete_res ((char *) res);
  res->next = 0;
  res->hash = last_hash;
  res->id = last_id;
  res->size = size;
  res->temporary = is_tmp;
  res->garbage = false;
  res->satisfied = is_taut;
  int *literals = res->literals, *p = literals;
  for (const auto &lit : simplified)
    *p++ = lit;
  num_clauses++;
  if (is_tmp)
    num_temporary++;
  else
    num_permanent++;

  // First two literals are used as watches and should not be false.
  //
  if (res->size > 1 && !is_taut) {
    for (unsigned i = 0; i < 2; i++) {
      int lit = literals[i];
      if (!val (lit))
        continue;
      for (unsigned j = i + 1; j < size; j++) {
        int other = literals[j];
        if (val (other))
          continue;
        swap (literals[i], literals[j]);
        break;
      }
    }
    assert (!val (literals[0]));
    assert (!val (literals[1]));
    watcher (literals[0]).push_back (CheckerWatch (literals[1], res));
    watcher (literals[1]).push_back (CheckerWatch (literals[0], res));
  }
  delete_res.release ();
  return res;
}

void Checker::move_to_garbage (CheckerClause **res) {
  CheckerClause *tmp = *res;
  // Remove from hash table, mark as garbage, connect to garbage list.
  num_garbage++;
  assert (num_clauses);
  num_clauses--;
  if (tmp->temporary)
    num_temporary--;
  else
    num_permanent--;
  *res = tmp->next;
  tmp->next = garbage;
  garbage = tmp;
  tmp->garbage = true;
}

void Checker::delete_clause (CheckerClause *c) {
  if (!c->garbage) {
    assert (num_clauses);
    num_clauses--;
    if (c->temporary)
      num_temporary--;
    else
      num_permanent--;
  } else {
    assert (num_garbage);
    num_garbage--;
  }
  delete[] (char *) c;
}

void Checker::enlarge_clauses () {
  assert (num_clauses == size_clauses);
  const uint64_t new_size_clauses = size_clauses ? 2 * size_clauses : 1;
  LOG ("CHECKER enlarging clauses of checker from %" PRIu64 " to %" PRIu64,
       (uint64_t) size_clauses, (uint64_t) new_size_clauses);
  CheckerClause **new_clauses;
  new_clauses = new CheckerClause *[new_size_clauses];
  clear_n (new_clauses, new_size_clauses);
  for (uint64_t i = 0; i < size_clauses; i++) {
    for (CheckerClause *c = clauses[i], *next; c; c = next) {
      next = c->next;
      const uint64_t h = reduce_hash (c->hash, new_size_clauses);
      c->next = new_clauses[h];
      new_clauses[h] = c;
    }
  }
  delete[] clauses;
  clauses = new_clauses;
  size_clauses = new_size_clauses;
}

inline bool Checker::clause_satisfied (CheckerClause *c) {
  if (c->garbage)
    return false;
  if (c->satisfied)
    return true;
  for (unsigned i = 0; i < c->size; i++)
    if (val (c->literals[i]) > 0)
      return true;
  return false;
}

// The main reason why we have an explicit garbage collection phase is that
// removing clauses from watcher lists eagerly might lead to an accumulated
// quadratic algorithm.  Thus we delay removing garbage clauses from watcher
// lists until garbage collection (even though we remove garbage clauses on
// the fly during propagation too).  We also remove satisfied clauses.
//
void Checker::collect_garbage_clauses () {

  stats.collections++;

  for (size_t i = 0; i < size_clauses; i++) {
    CheckerClause **p = clauses + i, *c;
    while ((c = *p)) {
      if (clause_satisfied (c))
        c->satisfied = true;
      p = &c->next;
    }
  }

  LOG ("CHECKER collecting %" PRIu64 " garbage clauses %.0f%%", num_garbage,
       percent (num_garbage, num_clauses));

  for (int lit = -size_vars + 1; lit < size_vars; lit++) {
    if (!lit)
      continue;
    CheckerWatcher &ws = watcher (lit);
    const auto end = ws.end ();
    auto j = ws.begin (), i = j;
    for (; i != end; i++) {
      CheckerWatch &w = *i;
      if (!w.clause->garbage && !w.clause->satisfied)
        *j++ = w;
    }
    if (j == ws.end ())
      continue;
    if (j == ws.begin ())
      erase_vector (ws);
    else
      ws.resize (j - ws.begin ());
  }

  for (CheckerClause *c = garbage, *next; c; c = next)
    next = c->next, delete_clause (c);

  assert (!num_garbage);
  garbage = 0;
}

/*------------------------------------------------------------------------*/

Checker::Checker (Internal *i, bool frat)
    : internal (i), check_finalize (frat), size_vars (0), vals (0),
      assumed (0), inconsistent (0), tmp_inconsistent (0), solving (false),
      num_clauses (0), num_garbage (0), num_finalized (0),
      num_temporary (0), num_permanent (0), size_clauses (0), clauses (0),
      garbage (0), next_to_propagate (0), last_hash (0), last_id (0),
      is_tmp (false), is_taut (false) {

  // Initialize random number table for hash function.
  //
  Random random (42);
  for (unsigned n = 0; n < num_nonces; n++) {
    uint64_t nonce = random.next ();
    if (!(nonce & 1))
      nonce++;
    assert (nonce), assert (nonce & 1);
    nonces[n] = nonce;
  }

  memset (&stats, 0, sizeof (stats)); // Initialize statistics.
}

void Checker::connect_internal (Internal *i) {
  internal = i;
  LOG ("CHECKER connected to internal");
}

Checker::~Checker () {
  LOG ("CHECKER delete");
  vals -= size_vars;
  delete[] vals;
  assumed -= size_vars;
  delete[] assumed;
  for (size_t i = 0; i < size_clauses; i++)
    for (CheckerClause *c = clauses[i], *next; c; c = next)
      next = c->next, delete_clause (c);
  for (CheckerClause *c = garbage, *next; c; c = next)
    next = c->next, delete_clause (c);
  delete[] clauses;
}

/*------------------------------------------------------------------------*/

// The simplicity for accessing 'vals' and 'watchers' directly through a
// signed integer literal, comes with the price of slightly more complex
// code in deleting and enlarging the checker data structures.

void Checker::enlarge_vars (int64_t idx) {

  assert (0 < idx), assert (idx <= INT_MAX);

  int64_t new_size_vars = size_vars ? 2 * size_vars : 2;
  while (idx >= new_size_vars)
    new_size_vars *= 2;
  LOG ("CHECKER enlarging variables of checker from %" PRId64 " to %" PRId64
       "",
       size_vars, new_size_vars);

  signed char *new_vals;
  new_vals = new signed char[2 * new_size_vars];
  clear_n (new_vals, 2 * new_size_vars);
  new_vals += new_size_vars;
  if (size_vars) // To make sanitizer happy (without '-O').
    memcpy ((void *) (new_vals - size_vars), (void *) (vals - size_vars),
            2 * size_vars);
  vals -= size_vars;
  delete[] vals;
  vals = new_vals;

  bool *new_assumed;
  new_assumed = new bool[2 * new_size_vars];
  clear_n (new_assumed, 2 * new_size_vars);
  new_assumed += new_size_vars;
  if (size_vars) // To make sanitizer happy (without '-O').
    memcpy ((void *) (new_assumed - size_vars),
            (void *) (assumed - size_vars), 2 * size_vars);
  assumed -= size_vars;
  delete[] assumed;
  assumed = new_assumed;

  size_vars = new_size_vars;

  watchers.resize (2 * new_size_vars);
  marks.resize (2 * new_size_vars);

  assert (idx < new_size_vars);
}

struct lit_smaller {
  bool operator() (int a, int b) const {
    int c = abs (a), d = abs (b);
    if (c < d)
      return true;
    if (c > d)
      return false;
    return a < b;
  }
};

bool Checker::tautological () {
  sort (simplified.begin (), simplified.end (), lit_smaller ());
  const auto end = simplified.end ();
  auto j = simplified.begin ();
  int prev = 0;
  bool sat = false;
  for (auto i = j; i != end; i++) {
    int lit = *i;
    if (lit == prev)
      continue; // duplicated literal
    if (lit == -prev)
      return true; // tautological clause
    const signed char tmp = val (lit);
    if (tmp > 0)
      sat = true; // satisfied literal and clause
    *j++ = prev = lit;
  }
  simplified.resize (j - simplified.begin ());
  return sat;
}

inline void Checker::import_literal (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  int idx = abs (lit);
  if (idx >= size_vars)
    enlarge_vars (idx);
  simplified.push_back (lit);
  unsimplified.push_back (lit);
}

void Checker::import_clause (const vector<int> &c, int64_t id,
                             bool temporary) {
  assert (simplified.empty ());
  assert (unsimplified.empty ());
  // simplified.clear ();   // Can be non-empty if clause allocation fails.
  // unsimplified.clear (); // Can be non-empty if clause allocation fails.
  for (const auto &lit : c)
    import_literal (lit);
  is_taut = tautological ();
  is_tmp = temporary;
  last_id = id;
}

/*------------------------------------------------------------------------*/

uint64_t Checker::reduce_hash (uint64_t hash, uint64_t size) {
  assert (size > 0);
  unsigned shift = 32;
  uint64_t res = hash;
  while ((((uint64_t) 1) << shift) > size) {
    res ^= res >> shift;
    shift >>= 1;
  }
  res &= size - 1;
  assert (res < size);
  return res;
}

uint64_t Checker::compute_hash () {
  unsigned j = last_id % num_nonces;
  uint64_t tmp = nonces[j] * last_id;
  return last_hash = tmp;
}

CheckerClause **Checker::find (int64_t id, bool check_lits) {
  stats.searches++;
  CheckerClause **res, *c;
  const uint64_t hash = compute_hash ();
  // const int64_t id = last_id;
  const unsigned size = simplified.size ();
  const uint64_t h = reduce_hash (hash, size_clauses);
  for (const auto &lit : simplified)
    mark (lit) = true;
  for (res = clauses + h; (c = *res); res = &c->next) {
    if (c->hash == hash && c->id == id && !check_lits)
      break;
    if (c->hash == hash && c->id == id && c->size == size) {
      bool found = true;
      const int *literals = c->literals;
      for (unsigned i = 0; found && i != size; i++)
        found = mark (literals[i]);
      if (found)
        break;
    }
    stats.collisions++;
  }
  for (const auto &lit : simplified)
    mark (lit) = false;
  return res;
}

void Checker::insert () {
  stats.insertions++;
  if (num_clauses == size_clauses)
    enlarge_clauses ();
  const uint64_t h = reduce_hash (compute_hash (), size_clauses);
  CheckerClause *c = new_clause ();
  c->next = clauses[h];
  clauses[h] = c;
}

/*------------------------------------------------------------------------*/

inline void Checker::assign (int lit) {
  assert (!val (lit));
  vals[lit] = 1;
  vals[-lit] = -1;
  trail.push_back (lit);
}

inline void Checker::assume (int lit) {
  signed char tmp = val (lit);
  if (tmp > 0)
    return;
  assert (!tmp);
  stats.assumptions++;
  assign (lit);
}

void Checker::backtrack (unsigned previously_propagated) {

  assert (previously_propagated <= trail.size ());

  while (trail.size () > previously_propagated) {
    int lit = trail.back ();
    assert (val (lit) > 0);
    assert (val (-lit) < 0);
    vals[lit] = vals[-lit] = 0;
    trail.pop_back ();
  }

  trail.resize (previously_propagated);
  next_to_propagate = previously_propagated;
  assert (trail.size () == next_to_propagate);
}

/*------------------------------------------------------------------------*/

// This is a standard propagation routine without using blocking literals
// nor without saving the last replacement position.

bool Checker::propagate (bool propagate_temporary) {
  bool res = true;
  while (res && next_to_propagate < trail.size ()) {
    int lit = trail[next_to_propagate++];
    stats.propagations++;
    assert (val (lit) > 0);
    assert (abs (lit) < size_vars);
    CheckerWatcher &ws = watcher (-lit);
    const auto end = ws.end ();
    auto j = ws.begin (), i = j;
    for (; res && i != end; i++) {
      CheckerWatch &w = *j++ = *i;
      const int blit = w.blit;
      const bool temporary = w.temporary;
      if (!propagate_temporary && temporary)
        continue;
      assert (blit != -lit);
      const signed char blit_val = val (blit);
      if (blit_val > 0)
        continue;
      const unsigned size = w.size;
      if (size == 2) { // not precise since
        if (blit_val < 0)
          res = false; // clause might be garbage
        else
          assign (w.blit); // but still sound
      } else {
        assert (size > 2);
        CheckerClause *c = w.clause;
        if (c->garbage || c->satisfied) {
          j--;
          continue;
        } // skip garbage and satisfied clauses
        assert (size == c->size);
        int *lits = c->literals;
        int other = lits[0] ^ lits[1] ^ (-lit);
        assert (other != -lit);
        signed char other_val = val (other);
        if (other_val > 0) {
          j[-1].blit = other;
          continue;
        }
        lits[0] = other, lits[1] = -lit;
        unsigned k;
        int replacement = 0;
        signed char replacement_val = -1;
        for (k = 2; k < size; k++)
          if ((replacement_val = val (replacement = lits[k])) >= 0)
            break;
        if (replacement_val >= 0) {
          watcher (replacement).push_back (CheckerWatch (-lit, c));
          swap (lits[1], lits[k]);
          j--;
        } else if (!other_val)
          assign (other);
        else
          res = false;
      }
    }
    while (i != end)
      *j++ = *i++;
    ws.resize (j - ws.begin ());
  }
  return res;
}

bool Checker::check (bool propagate_temporary) {
  stats.checks++;
  if (inconsistent)
    return true;
  if (propagate_temporary && tmp_inconsistent)
    return true;
  if (is_taut)
    return true;
  unsigned previously_propagated = next_to_propagate;
  if (propagate_temporary) {
    for (const auto &lit : temporary_units) {
      if (val (lit) > 0) // implicit in 'assume'
        continue;
      if (val (lit) < 0) {
        assert (!tmp_inconsistent);
        tmp_inconsistent = -1;
        backtrack (previously_propagated);
        return true;
      }
      assume (lit);
    }
  }
  for (const auto &lit : simplified) {
    if (propagate_temporary && val (lit) > 0) {
      assert (!tmp_inconsistent);
      tmp_inconsistent = -1;
      backtrack (previously_propagated);
      return true;
    }
    assume (-lit);
  }
  bool res = !propagate (propagate_temporary);
  backtrack (previously_propagated);
  return res;
}

bool Checker::check_blocked () {
  for (const auto &lit : unsimplified) {
    mark (-lit) = true;
  }
  vector<int> not_blocked;
  for (size_t i = 0; i < size_clauses; i++) {
    for (CheckerClause *c = clauses[i], *next; c; c = next) {
      assert (!c->garbage);
      next = c->next;
      unsigned count = 0;
      int first;
      for (int *i = c->literals; i < c->literals + c->size; i++) {
        const int lit = *i;
        if (val (lit) > 0) {
          count = 2;
          break;
        }
        if (mark (lit)) {
          count++;
          first = lit;
        }
      }
      if (count == 1) {
        not_blocked.push_back (first);
        LOG (c->literals, c->size, "CHECKER non-blocked %d clause", first);
      }
    }
  }
  for (const auto &lit : not_blocked) {
    mark (lit) = false;
  }
  bool blocked = false;
  for (const auto &lit : unsimplified) {
    if (mark (-lit))
      blocked = true;
    mark (-lit) = false;
  }
  return blocked;
}

/*------------------------------------------------------------------------*/

void Checker::add_clause (const char *type) {
#ifndef LOGGING
  (void) type;
#endif
  // If there are enough garbage clauses collect them first.
  if (num_garbage > 0.5 * max ((size_t) size_clauses, (size_t) size_vars))
    collect_garbage_clauses ();

  int unit = 0;
  if (is_taut) {
    unit = INT_MIN;
  } else {
    for (const auto &lit : simplified) {
      const signed char tmp = val (lit);
      if (tmp < 0)
        continue;
      if (tmp > 0) {
        unit = INT_MIN;
        break;
      }
      assert (!tmp);
      if (unit) {
        unit = INT_MIN;
        break;
      }
      unit = lit;
    }
  }

  if (simplified.empty ()) {
    LOG ("CHECKER added empty %s clause", type);
    if (is_tmp)
      tmp_inconsistent = last_id;
    else
      inconsistent = last_id;
    is_taut = true;
  }
  if (!unit) {
    LOG ("CHECKER added and checked falsified %s clause", type);
    if (!is_tmp && !inconsistent)
      inconsistent = -1;
    else if (is_tmp && !tmp_inconsistent)
      tmp_inconsistent = -1;
    is_taut = true;
  } else if (unit != INT_MIN) {
    LOG ("CHECKER added and checked %s unit clause %d", type, unit);
    if (is_tmp) {
      temporary_units.push_back (unit);
    } else {
      assign (unit);
      stats.units++;
      if (!propagate (false)) {
        LOG ("CHECKER inconsistent after propagating %s unit", type);
        if (!inconsistent)
          inconsistent = -1;
      }
    }
    is_taut = true;
  }
  insert ();
  simplified.clear ();
  unsimplified.clear ();
}

void Checker::add_original_clause (int64_t id, bool, const vector<int> &c,
                                   bool) {
  PROFILE_SCOPE (checking);
  LOG (c, "CHECKER addition of original clause");
  stats.added++;
  stats.original++;
  import_clause (c, id, false);
  add_clause ("original");
}

void Checker::add_derived_clause (int64_t id, bool redundant, int witness,
                                  const vector<int> &c,
                                  const vector<int64_t> &) {
  PROFILE_SCOPE (checking);
  LOG (c, "CHECKER addition of derived clause");
  stats.added++;
  stats.derived++;
  stats.derived_redundant += redundant;
  stats.derived_irredundant += !redundant;
  import_clause (c, id, false);
  if (is_taut)
    LOG ("CHECKER ignoring satisfied derived clause");
  else if (!witness && !check ()) {
    fatal_message_start ();
    fputs ("failed to check derived clause:\n", stderr);
    for (const auto &lit : unsimplified)
      fprintf (stderr, "%d ", lit);
    fputc ('0', stderr);
    fatal_message_end ();
  } else if (witness && !check_blocked ()) {
    fatal_message_start ();
    fputs ("failed to check derived clause:\n", stderr);
    for (const auto &lit : unsimplified)
      fprintf (stderr, "%d ", lit);
    fputc ('0', stderr);
    fatal_message_end ();
  }
  add_clause ("derived");
}

/*------------------------------------------------------------------------*/

void Checker::delete_clause (int64_t id, bool, const vector<int> &c) {
  PROFILE_SCOPE (checking);
  LOG (c, "CHECKER checking deletion of clause");
  stats.deleted++;
  import_clause (c, id, false);
  CheckerClause **p = find (id, true), *d = *p;
  if (d) {
    // Remove from hash table, mark as garbage, connect to garbage list.
    move_to_garbage (p);
  } else {
    fatal_message_start ();
    fputs ("deleted clause not in proof:\n", stderr);
    for (const auto &lit : unsimplified)
      fprintf (stderr, "%d ", lit);
    fputc ('0', stderr);
    fatal_message_end ();
  }
  simplified.clear ();
  unsimplified.clear ();
}

void Checker::add_assumption_clause (int64_t id, const vector<int> &c,
                                     const vector<int64_t> &) {
  PROFILE_SCOPE (checking);
  LOG (c, "CHECKER checking addition of assumption clause");
  import_clause (c, id, true);
  if (!check (false)) {
    fatal_message_start ();
    fputs ("failed to check assumption clause:\n", stderr);
    for (const auto &lit : unsimplified)
      fprintf (stderr, "%d ", lit);
    fputc ('0', stderr);
    fatal_message_end ();
  }
  add_clause ("assumption");
  assumption_clauses.push_back (id);
}

void Checker::add_constraint_clause (int64_t id, const vector<int> &c,
                                     const vector<int64_t> &) {
  PROFILE_SCOPE (checking);
  LOG (c, "CHECKER checking addition of derived constraint clause");
  import_clause (c, id, true);
  if (!check (true)) {
    fatal_message_start ();
    fputs ("failed to check constraint clause:\n", stderr);
    for (const auto &lit : unsimplified)
      fprintf (stderr, "%d ", lit);
    fputc ('0', stderr);
    fatal_message_end ();
  }
  add_clause ("derived constraint");
  assumption_clauses.push_back (id);
}

// TODO: Semantics of these three?
void Checker::demote_clause (int64_t, const std::vector<int> &) {}
void Checker::weaken_minus (int64_t, const std::vector<int> &) {}
void Checker::strengthen (int64_t) {}

// TODO: restrict interactions? e.g. no reset_assumptions before any
// type of conclusion
void Checker::solve_query () { solving = true; }

// TODO: import constraint as temporary clause which is only propagated
// for add_assumption_clause checks.
void Checker::add_constraint (int64_t id, const std::vector<int> &c) {
  PROFILE_SCOPE (checking);
  LOG (c, "CHECKER adding constraint");
  import_clause (c, id, true);
  add_clause ("original constraint");
  assumption_clauses.push_back (id);
}

void Checker::add_assumption (int a) {
  PROFILE_SCOPE (checking);
  LOG ("CHECKER adding assumptions %d", a);
  assert (a);
  assert (a != INT_MIN);
  int idx = abs (a);
  if (idx >= size_vars)
    enlarge_vars (idx);
  if (assumed[a])
    return;
  assumed[a] = true;
  assumptions.push_back (a);
}

void Checker::reset_assumptions () {
  PROFILE_SCOPE (checking);
  LOG ("CHECKER resetting assumptions");
  if (solving)
    fatal ("can not 'reset_assumptions' before 'conclude'");
  for (auto &id : assumption_clauses) {
    // find and delete id.
    last_id = id;
    CheckerClause **p = find (id, false), *d = *p;
    if (d) {
      assert (d->temporary);
      // Remove from hash table, mark as garbage, connect to garbage list.
      move_to_garbage (p);
    } else {
      LOG ("error, did not find assumption clause %" PRId64, id);
      assert (false);
    }
  }
  assumption_clauses.clear ();
  for (auto &a : assumptions) {
    assert (assumed[a]);
    assumed[a] = 0;
  }
  assumptions.clear ();
}

// TODO: check that conclusion clauses exist and last one is directly
// falsified by query assumptions
void Checker::conclude_unsat (ConclusionType,
                              const std::vector<int64_t> &ids) {
  PROFILE_SCOPE (checking);
  LOG ("CHECKER checking conclusion");
  if (!solving)
    fatal ("can not 'conclude_unsat' before 'solve_query'");
  solving = false;
  bool falsified = false;
  for (auto &id : ids) {
    /*
    if (inconsistent && id == inconsistent) {
      falsified = true;
      break;
    }
    if (tmp_inconsistent && id == tmp_inconsistent) {
      falsified = true;
      break;
    }
    */
    last_id = id;
    CheckerClause **p = find (id, false), *d = *p;
    if (!d)
      fatal ("did not find conclusion clause[%" PRId64 "]", id);
    if (!d->size)
      falsified = true;
    else if (!falsified) {
      // falsified by assumptions
      falsified = true;
      for (size_t i = 0; i < d->size; i++) {
        const int lit = d->literals[i];
        if (!assumed[-lit]) {
          falsified = false;
          break;
        }
      }
    }
  }
  if (!falsified) {
    fatal_message_start ();
    fputs ("failed conclude_unsat, no clause from ", stderr);
    for (const auto &id : ids)
      fprintf (stderr, "%" PRId64 ", ", id);
    fputs ("contradicts with assumptions ", stderr);
    for (const auto &lit : assumptions)
      fprintf (stderr, "%d, ", lit);
    fatal_message_end ();
  }
}

// TODO: check that model satisfies formula
void Checker::conclude_sat (const std::vector<int> &) {
  PROFILE_SCOPE (checking);
  if (!solving)
    fatal ("can not 'conclude_sat' before 'solve_query'");
  solving = false;
}

// TODO: check that query assumptions -> trail
void Checker::conclude_unknown (const std::vector<int> &) {
  PROFILE_SCOPE (checking);
  if (!solving)
    fatal ("can not 'conclude_unknown' before 'solve_query'");
  solving = false;
}

// check both sides of the equivalence but do not add to the clause set.
void Checker::notify_equivalence (int a, int b) {
  PROFILE_SCOPE (checking);
  LOG ("CHECKER checking equivalence of %d and %d", a, b);
  vector<int> c;
  c.push_back (-a);
  c.push_back (b);
  import_clause (c, 0, true);
  if (!check ()) {
    fatal_message_start ();
    fprintf (stderr, "failed to check implication %d -> %d\n", -a, b);
    fatal_message_end ();
  }
  simplified.clear ();
  unsimplified.clear ();
  c.clear ();
  c.push_back (a);
  c.push_back (-b);
  import_clause (c, 0, true);
  if (!check ()) {
    fatal_message_start ();
    fprintf (stderr, "failed to check implication %d -> %d\n", a, -b);
    fatal_message_end ();
  }
  simplified.clear ();
  unsimplified.clear ();
}

void Checker::finalize_clause (int64_t id, const vector<int> &c) {
  if (!check_finalize)
    return;
  PROFILE_SCOPE (checking);
  LOG (c, "CHECKER checking finalize of clause[%" PRId64 "]", id);
  stats.finalized++;
  num_finalized++;
  import_clause (c, id, false);
  CheckerClause **p = find (id, true), *d = *p;
  if (!d) {
    fatal_message_start ();
    fputs ("finalized clause not in proof:\n", stderr);
    for (const auto &lit : simplified)
      fprintf (stderr, "%d ", lit);
    fputc ('0', stderr);
    fatal_message_end ();
  }
  unsimplified.clear ();
  simplified.clear ();
}

// check if all clauses have been deleted
void Checker::report_status (int, int64_t) {
  if (!check_finalize)
    return;
  PROFILE_SCOPE (checking);
  if (num_finalized == num_permanent) {
    num_finalized = 0;
    LOG ("CHECKER successful finalize check, all clauses have been "
         "finalized");
  } else {
    fatal_message_start ();
    fputs ("finalize check failed ", stderr);
    fprintf (stderr, "%" PRIu64, num_permanent);
    fputs (" are not finalized", stderr);
    fatal_message_end ();
  }
}

/*------------------------------------------------------------------------*/

void Checker::dump () {
  int max_var = 0;
  for (uint64_t i = 0; i < size_clauses; i++)
    for (CheckerClause *c = clauses[i]; c; c = c->next)
      for (unsigned i = 0; i < c->size; i++)
        if (abs (c->literals[i]) > max_var)
          max_var = abs (c->literals[i]);
  printf ("p cnf %d %" PRIu64 "\n", max_var, num_clauses);
  for (uint64_t i = 0; i < size_clauses; i++)
    for (CheckerClause *c = clauses[i]; c; c = c->next) {
      for (unsigned i = 0; i < c->size; i++)
        printf ("%d ", c->literals[i]);
      printf ("0\n");
    }
}

} // namespace CaDiCaL
