#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

inline unsigned LratBuilder::l2u (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  unsigned res = 2 * (abs (lit) - 1);
  if (lit < 0)
    res++;
  return res;
}

inline unsigned LratBuilder::l2a (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  unsigned res = abs (lit);
  return res;
}

inline signed char LratBuilder::val (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  assert (abs (lit) < size_vars);
  assert (vals[lit] == -vals[-lit]);
  return vals[lit];
}

signed char &LratBuilder::mark (int lit) {
  const unsigned u = l2u (lit);
  assert (u < marks.size ());
  return marks[u];
}

signed char &LratBuilder::checked_lit (int lit) {
  const unsigned u = l2u (lit);
  assert (u < checked_lits.size ());
  return checked_lits[u];
}

inline LratBuilderWatcher &LratBuilder::watcher (int lit) {
  const unsigned u = l2u (lit);
  assert (u < watchers.size ());
  return watchers[u];
}

/*------------------------------------------------------------------------*/
LratBuilderClause *LratBuilder::new_clause () {
  const size_t size = simplified.size ();
  assert (size <= UINT_MAX);
  const int off = size ? 1 : 0;
  const size_t bytes =
      sizeof (LratBuilderClause) + (size - off) * sizeof (int);
  LratBuilderClause *res = (LratBuilderClause *) new char[bytes];
  DeferDeleteArray<char> delete_res ((char *) res);
  res->garbage = false;
  res->next = 0;
  res->hash = last_hash;
  res->id = last_id;
  res->size = size;
  num_clauses++;
  int *literals = res->literals, *p = literals;
  for (const auto &lit : simplified)
    *p++ = lit;

  if (size == 0) {
    delete_res.release ();
    return res;
  }
  if (size == 1) {
    unit_clauses.push_back (res);
    delete_res.release ();
    return res;
  }

  // First two literals are used as watches and should not be false.
  // or at least one should be true. But we can have falsified clauses
  // then we cannot guarantee anything here.
  //
  for (unsigned i = 0; i < 2; i++) {
    int lit = literals[i];
    if (val (lit) >= 0)
      continue;
    for (unsigned j = i + 1; j < size; j++) {
      int other = literals[j];
      if (val (other) < 0)
        continue;
      swap (literals[i], literals[j]);
      break;
    }
  }

  // make sure the clause is not tautological
  if (!new_clause_taut) {
    watcher (literals[0]).push_back (LratBuilderWatch (literals[1], res));
    watcher (literals[1]).push_back (LratBuilderWatch (literals[0], res));
  } else {
    LOG ("LRAT BUILDER clause not added to watchers");
  }
  delete_res.release ();
  return res;
}

void LratBuilder::delete_clause (LratBuilderClause *c) {
  assert (c);
  if (!c->garbage) {
    assert (num_clauses);
    num_clauses--;
  } else {
    assert (num_garbage);
    num_garbage--;
  }
  delete[] (char *) c;
}

void LratBuilder::enlarge_clauses () {
  assert (num_clauses == size_clauses);
  const uint64_t new_size_clauses = size_clauses ? 2 * size_clauses : 1;
  LOG ("LRAT BUILDER enlarging clauses of checker from %" PRIu64
       " to %" PRIu64,
       (uint64_t) size_clauses, (uint64_t) new_size_clauses);
  LratBuilderClause **new_clauses;
  new_clauses = new LratBuilderClause *[new_size_clauses];
  clear_n (new_clauses, new_size_clauses);
  for (uint64_t i = 0; i < size_clauses; i++) {
    for (LratBuilderClause *c = clauses[i], *next; c; c = next) {
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

bool LratBuilder::clause_satisfied (LratBuilderClause *c) {
  for (unsigned i = 0; i < c->size; i++)
    if (val (c->literals[i]) > 0)
      return true;
  return false;
}

bool LratBuilder::clause_falsified (LratBuilderClause *c) {
  for (unsigned i = 0; i < c->size; i++)
    if (val (c->literals[i]) >= 0)
      return false;
  return true;
}

// The main reason why we have an explicit garbage collection phase is that
// removing clauses from watcher lists eagerly might lead to an accumulated
// quadratic algorithm.  Thus we delay removing garbage clauses from watcher
// lists until garbage collection (even though we remove garbage clauses on
// the fly during propagation too).  We also remove satisfied clauses.
//
// Problem: this should only happen in DRAT not in lrat!! Done.
//
void LratBuilder::collect_garbage_clauses () {

  stats.collections++;

  LOG ("LRAT BUILDER collecting %" PRIu64 " garbage clauses %.0f%%",
       num_garbage, percent (num_garbage, num_clauses));

  for (int lit = -size_vars + 1; lit < size_vars; lit++) {
    if (!lit)
      continue;
    LratBuilderWatcher &ws = watcher (lit);
    const auto end = ws.end ();
    auto j = ws.begin (), i = j;
    for (; i != end; i++) {
      LratBuilderWatch &w = *i;
      if (!w.clause->garbage)
        *j++ = w;
    }
    if (j == ws.end ())
      continue;
    if (j == ws.begin ())
      erase_vector (ws);
    else
      ws.resize (j - ws.begin ());
  }

  const auto end = unit_clauses.end ();
  auto j = unit_clauses.begin ();
  for (auto i = j; i != end; i++) {
    LratBuilderClause *c = *i;
    if (c->garbage)
      continue; // garbage clause
    *j++ = c;
  }
  unit_clauses.resize (j - unit_clauses.begin ());

  for (LratBuilderClause *c = garbage, *next; c; c = next)
    next = c->next, delete_clause (c);

  assert (!num_garbage);
  garbage = 0;
}

/*------------------------------------------------------------------------*/

LratBuilder::LratBuilder (Internal *i)
    : internal (i), size_vars (0), vals (0), new_clause_taut (0),
      inconsistent (false), num_clauses (0), num_garbage (0),
      size_clauses (0), clauses (0), garbage (0), next_to_propagate (0),
      last_hash (0), last_id (0) {
  LOG ("LRAT BUILDER new");

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

  const size_t bytes = sizeof (LratBuilderClause);
  assumption = (LratBuilderClause *) new char[bytes]; // assumption clause
  assumption->garbage = false;
  assumption->next = 0;
  assumption->hash = 0;
  assumption->id = 0;
  assumption->size = 0;
}

LratBuilder::~LratBuilder () {
  LOG ("LRAT BUILDER delete");
  vals -= size_vars;
  delete[] vals;
  for (size_t i = 0; i < size_clauses; i++)
    for (LratBuilderClause *c = clauses[i], *next; c; c = next)
      next = c->next, delete_clause (c);
  for (LratBuilderClause *c = garbage, *next; c; c = next)
    next = c->next, delete_clause (c);
  delete[] clauses;
  num_clauses++;
  delete_clause (assumption);
}

/*------------------------------------------------------------------------*/

// The simplicity for accessing 'vals' and 'watchers' directly through a
// signed integer literal, comes with the price of slightly more complex
// code in deleting and enlarging the checker data structures.

void LratBuilder::enlarge_vars (int64_t idx) {

  assert (0 < idx), assert (idx <= INT_MAX);

  int64_t new_size_vars = size_vars ? 2 * size_vars : 2;
  while (idx >= new_size_vars)
    new_size_vars *= 2;
  LOG ("LRAT BUILDER enlarging variables of checker from %" PRId64
       " to %" PRId64 "",
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
  size_vars = new_size_vars;

  reasons.resize (new_size_vars);
  unit_reasons.resize (new_size_vars);
  justified.resize (new_size_vars);
  todo_justify.resize (new_size_vars);
  for (int64_t i = size_vars; i < new_size_vars; i++) {
    reasons[i] = 0;
    unit_reasons[i] = 0;
    justified[i] = 0;
    todo_justify[i] = 0;
  }

  watchers.resize (2 * new_size_vars);
  marks.resize (2 * new_size_vars);
  checked_lits.resize (2 * new_size_vars);

  assert (idx < new_size_vars);
}

inline void LratBuilder::import_literal (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  int idx = abs (lit);
  if (idx >= size_vars)
    enlarge_vars (idx);
  simplified.push_back (lit);
  unsimplified.push_back (lit);
}

void LratBuilder::import_clause (const vector<int> &c) {
  for (const auto &lit : c)
    import_literal (lit);
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

void LratBuilder::tautological () {
  sort (simplified.begin (), simplified.end (), lit_smaller ());
  const auto end = simplified.end ();
  auto j = simplified.begin ();
  int prev = 0;
  for (auto i = j; i != end; i++) {
    int lit = *i;
    if (lit == prev)
      continue; // duplicated literal
    if (lit == -prev) {
      new_clause_taut = true;
      return;
    } // tautological clause
    *j++ = prev = lit; // which means we don't care
  }
  simplified.resize (j - simplified.begin ());
}

/*------------------------------------------------------------------------*/

uint64_t LratBuilder::reduce_hash (uint64_t hash, uint64_t size) {
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

uint64_t LratBuilder::compute_hash (const uint64_t id) {
  assert (id > 0);
  unsigned j = id % num_nonces;             // Don't know if this is a good
  uint64_t tmp = nonces[j] * (uint64_t) id; // hash function or even better
  return last_hash = tmp;                   // than just using id.
}

LratBuilderClause **LratBuilder::find (const uint64_t id) {
  stats.searches++;
  LratBuilderClause **res, *c;
  const uint64_t hash = compute_hash (id);
  const uint64_t h = reduce_hash (hash, size_clauses);
  for (res = clauses + h; (c = *res); res = &c->next) {
    if (c->hash == hash && c->id == id) {
      break;
    }
    stats.collisions++;
  }
  return res;
}

LratBuilderClause *LratBuilder::insert () {
  stats.insertions++;
  if (num_clauses == size_clauses)
    enlarge_clauses ();
  const uint64_t h = reduce_hash (compute_hash (last_id), size_clauses);
  LratBuilderClause *c;
  c = new_clause ();
  c->next = clauses[h];
  clauses[h] = c;
  return c;
}

/*------------------------------------------------------------------------*/

inline void LratBuilder::assign (int lit) {
  assert (!val (
      lit)); // cannot guarantee (!val (lit)) anymore :/ -> yes we can!
  vals[lit] = 1;
  vals[-lit] = -1;
  trail.push_back (lit);
}

inline void LratBuilder::assume (int lit) {
  signed char tmp = val (lit);
  if (tmp > 0)
    return;
  assert (!tmp);
  reasons[l2a (lit)] = assumption;
  stats.assumptions++;
  assign (lit);
}

inline void LratBuilder::assign_reason (int lit,
                                        LratBuilderClause *reason_clause) {
  assert (!reasons[l2a (lit)]);
  reasons[l2a (lit)] = reason_clause;
  assign (lit);
}

inline void LratBuilder::unassign_reason (int lit) {
  assert (reasons[l2a (lit)]);
  reasons[l2a (lit)] = 0;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  vals[lit] = vals[-lit] = 0;
}

void LratBuilder::backtrack (unsigned previously_propagated) {

  assert (previously_propagated <= trail.size ());

  while (trail.size () > previously_propagated) {
    int lit = trail.back ();
    unassign_reason (lit);
    trail.pop_back ();
  }

  trail.resize (previously_propagated);
  next_to_propagate = previously_propagated;
  assert (trail.size () == next_to_propagate);
}

/*------------------------------------------------------------------------*/

bool LratBuilder::unit_propagate () {
  const auto end = unit_clauses.end ();
  bool res = true;
  auto j = unit_clauses.begin (), i = j;
  for (; res && i != end; i++) {
    LratBuilderClause *c = *j++ = *i;
    if (c->garbage) {
      j--;
      continue;
    } // skip garbage clauses
    assert (c->size == 1);
    int lit = c->literals[0];
    int value = val (lit);
    if (value > 0)
      continue;
    else if (!value)
      assign_reason (c->literals[0], c);
    else {
      res = false;
      conflict = c;
    }
  }
  while (i != end)
    *j++ = *i++;
  unit_clauses.resize (j - unit_clauses.begin ());
  return res;
}

// This is a standard propagation routine without using blocking literals
// nor without saving the last replacement position.
bool LratBuilder::propagate () {
  bool res = unit_propagate ();
  while (res && next_to_propagate < trail.size ()) {
    int lit = trail[next_to_propagate++];
    stats.propagations++;
    assert (val (lit) > 0);
    assert (abs (lit) < size_vars);
    LratBuilderWatcher &ws = watcher (-lit);
    const auto end = ws.end ();
    auto j = ws.begin (), i = j;
    for (; res && i != end; i++) {
      LratBuilderWatch &w = *j++ = *i;
      if (w.clause->garbage) {
        j--;
        continue;
      } // skip garbage clauses
      assert (w.size == w.clause->size);
      const int blit = w.blit;
      assert (blit != -lit);
      const signed char blit_val = val (blit);
      if (blit_val > 0)
        continue;
      const unsigned size = w.size;
      if (size == 1) { // should not happen
        if (blit_val < 0) {
          res = false;
          conflict = w.clause;
        } else
          assign_reason (w.blit, w.clause);
      } else if (size == 2) {
        if (blit_val < 0) {
          res = false;
          conflict = w.clause;
        } else
          assign_reason (w.blit, w.clause);
      } else {
        assert (size > 2);
        LratBuilderClause *c = w.clause;
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
          watcher (replacement).push_back (LratBuilderWatch (-lit, c));
          swap (lits[1], lits[k]);
          j--;
        } else if (!other_val)
          assign_reason (other, c);
        else {
          res = false;
          conflict = c;
        }
      }
    }
    while (i != end)
      *j++ = *i++;
    ws.resize (j - ws.begin ());
  }
  return res;
}

void LratBuilder::construct_chain () {
  LOG ("LRAT BUILDER checking lits on trail in reverse order");
  for (auto p = trail.end () - 1; unjustified && p >= trail.begin (); p--) {
    int lit = *p;
    if (!todo_justify[l2a (lit)]) {
      LOG ("LRAT BUILDER lit %d not needed", lit);
      continue;
    }
    if (justified[l2a (lit)]) {
      LOG ("LRAT BUILDER lit %d already justified", lit);
      unjustified--; // one of the todo_justify lits justified
      continue;
    }
    justified[l2a (lit)] = true;
    LOG ("LRAT BUILDER justify lit %d", lit);
    unjustified--; // one of the todo_justify lits justified
    LratBuilderClause *reason_clause = unit_reasons[l2a (lit)];
    if (!reason_clause)
      reason_clause = reasons[l2a (lit)];
    assert (reason_clause);
    assert (!reason_clause->garbage);
    reverse_chain.push_back (reason_clause->id);
    const int *rp = reason_clause->literals;
    for (unsigned i = 0; i < reason_clause->size; i++) {
      int reason_lit = *(rp + i);
      if (todo_justify[l2a (reason_lit)]) {
        LOG ("LRAT BUILDER lit %d already marked", reason_lit);
        continue;
      }
      if (justified[l2a (reason_lit)]) {
        LOG ("LRAT BUILDER lit %d already justified", reason_lit);
        continue;
      }
      LOG ("LRAT BUILDER need to justify lit %d", reason_lit);
      unjustified++; // new todo_justify means unjustified increase
      todo_justify[l2a (reason_lit)] = true;
    }
  }
  assert (!unjustified);
  for (auto p = reverse_chain.end () - 1; p >= reverse_chain.begin ();
       p--) {
    assert (*p);
    chain.push_back (*p);
  }
}

void LratBuilder::proof_tautological_clause () {
  LOG (simplified, "LRAT BUILDER tautological clause needs no proof:");
}

void LratBuilder::proof_satisfied_literal (int lit) {
  LOG ("LRAT BUILDER satisfied clause is proven by %d", lit);
  unjustified = 1; // is always > 0 if we have work to do
  todo_justify[l2a (lit)] = true;
  construct_chain ();
}

void LratBuilder::proof_inconsistent_clause () {
  LOG ("LRAT BUILDER inconsistent clause proves anything");
  if (inconsistent_chain.size ()) {
    for (auto &id : inconsistent_chain) {
      chain.push_back (id);
    }
    return;
  }

  unjustified =
      inconsistent_clause->size; // is always > 0 if we have work to do
  const int *end =
      inconsistent_clause->literals + inconsistent_clause->size;
  for (int *i = inconsistent_clause->literals; i < end; i++) {
    int lit = *i;
    todo_justify[l2a (lit)] = true;
  }
  reverse_chain.push_back (inconsistent_clause->id);
  construct_chain ();
  for (auto &id : chain) {
    inconsistent_chain.push_back (id);
  }
}

void LratBuilder::proof_clause () {
  LOG (simplified, "LRAT BUILDER LRAT building proof for");
  // marking clause as justified
  for (const auto &lit : simplified) {
    justified[l2a (lit)] = true;
  }
  unjustified = conflict->size; // is always > 0 if we have work to do
  const int *end = conflict->literals + conflict->size;
  for (int *i = conflict->literals; i < end; i++) {
    int lit = *i;
    todo_justify[l2a (lit)] = true;
  }
  reverse_chain.push_back (conflict->id);
  construct_chain ();
}

bool LratBuilder::build_chain_if_possible () {
  stats.checks++;

  chain.clear ();

  if (new_clause_taut) {
    proof_tautological_clause ();
    return true;
  }

  reverse_chain.clear ();
  for (size_t i = 0; i < justified.size (); i++)
    justified[i] = false;
  for (size_t i = 0; i < todo_justify.size (); i++)
    todo_justify[i] = false;

  if (inconsistent) {
    assert (inconsistent_clause);
    proof_inconsistent_clause ();
    return true;
  }
  unsigned previously_propagated = next_to_propagate;
  unsigned previous_trail_size = trail.size ();

  for (const auto &lit : simplified) {
    if (val (lit) > 0) {
      backtrack (previous_trail_size);
      next_to_propagate = previously_propagated;
      proof_satisfied_literal (lit);
      return true;
    } else if (!val (lit)) {
      assume (-lit);
    }
  }
  if (propagate ()) {
    backtrack (previous_trail_size);
    next_to_propagate = previously_propagated;
    return false;
  }

  proof_clause ();

  backtrack (previous_trail_size);
  next_to_propagate = previously_propagated;

  return true;
}

/*------------------------------------------------------------------------*/

void LratBuilder::clean () {
  simplified.clear ();
  unsimplified.clear ();
  new_clause_taut = false;
  conflict = 0;
}

void LratBuilder::add_clause (const char *type) {
#ifndef LOGGING
  (void) type;
#endif

  // If there are enough garbage clauses collect them.
  if (num_garbage > 0.5 * max ((size_t) size_clauses, (size_t) size_vars))
    collect_garbage_clauses ();

  LratBuilderClause *c = insert ();
  if (inconsistent) {
    LOG ("LRAT BUILDER state already inconsistent so nothing more to do");
    return;
  }

  const unsigned size = c->size;
  bool sat = clause_satisfied (c);
  int unit = 0;
  if (!sat) {
    const int *p = c->literals;
    for (unsigned i = 0; i < size; i++) {
      int lit = *(p + i);
      if (!val (lit)) {
        if (unit) {
          unit = INT_MIN;
          break;
        }
        unit = lit;
      }
    }
  }
  if (size == 1) {
    if (!val (c->literals[0]))
      unit_reasons[l2a (c->literals[0])] = c;
  }
  if (!size) {
    LOG ("LRAT BUILDER added and checked empty %s clause", type);
    LOG ("LRAT BUILDER clause with id %" PRIu64 " is now falsified", c->id);
    inconsistent = true;
    inconsistent_clause = c;
  } else if (sat) {
    LOG ("LRAT BUILDER added and checked satisfied %s clause", type);
  } else if (!unit) {
    LOG ("LRAT BUILDER added and checked falsified %s clause with id "
         "%" PRIu64,
         type, c->id);
    inconsistent = true;
    inconsistent_clause = c;
  } else if (unit == INT_MIN) {
    LOG ("LRAT BUILDER added and checked non unit %s clause", type);
  } else {
    stats.units++;
    LOG ("LRAT BUILDER checked and assigned %s unit clause %d", type, unit);
    assign_reason (unit, c);
    if (!propagate ()) {
      LOG ("LRAT BUILDER inconsistent after adding %s clause and "
           "propagating",
           type);
      LOG ("LRAT BUILDER clause with id %" PRIu64 " is now falsified",
           conflict->id);
      inconsistent = true;
      inconsistent_clause = conflict;
      assert (clause_falsified (conflict));
    }
  }
}

/*------------------------------------------------------------------------*/

void LratBuilder::add_original_clause (uint64_t id, const vector<int> &c) {
  START (checking);
  LOG (c, "LRAT BUILDER addition of original clause");
  LOG ("LRAT BUILDER clause id %" PRIu64, id);
  stats.added++;
  stats.original++;
  import_clause (c);
  last_id = id;
  assert (id);
  assert (!new_clause_taut);
  tautological ();
  add_clause ("original");
  clean ();
  STOP (checking);
}

const vector<uint64_t> &
LratBuilder::add_clause_get_proof (uint64_t id, const vector<int> &c) {
  START (checking);
  LOG (c, "LRAT BUILDER addition of derived clause");
  LOG ("LRAT BUILDER clause id %" PRIu64, id);
  stats.added++;
  stats.derived++;
  import_clause (c);
  last_id = id;
  assert (id);
  assert (!new_clause_taut);
  tautological ();

  bool res = build_chain_if_possible ();
  if (!res) {
    fatal_message_start ();
    fputs ("failed to build chain for clause:\n", stderr);
    for (const auto &lit : unsimplified)
      fprintf (stderr, "%d ", lit);
    fputc ('0', stderr);
    fatal_message_end ();
  } else
    add_clause ("derived");
  clean ();
  STOP (checking);
  return chain;
}

void LratBuilder::add_derived_clause (uint64_t id, const vector<int> &c) {
  START (checking);
  LOG (c, "LRAT BUILDER addition of derived clause");
  LOG ("LRAT BUILDER proceeding without proof chain building");
  stats.added++;
  import_clause (c);
  last_id = id;
  assert (id);
  assert (!new_clause_taut);
  tautological ();
  add_clause ("derived");
  clean ();
  STOP (checking);
}

void LratBuilder::delete_clause (uint64_t id, const vector<int> &c) {
  START (checking);
  LOG (c, "LRAT BUILDER checking deletion of clause");
  LOG ("LRAT BUILDER clause id %" PRIu64, id);
  stats.deleted++;
  import_clause (c);
  last_id = id;
  tautological ();
  LratBuilderClause **p = find (id), *d = *p;
  if (d) {
    // TODO: marks should only be defined and used in debugging mode
    for (const auto &lit : simplified)
      mark (lit) = true;
    int unit = 0;
    const int *dp = d->literals;
    for (unsigned i = 0; i < d->size; i++) {
      int lit = *(dp + i);
      assert (mark (lit));
      LratBuilderClause *reason = reasons[l2a (lit)];
      if (!val (lit))
        LOG ("LRAT BUILDER skipping lit %d not assigned", lit);
      else
        LOG ("LRAT BUILDER lit %d reason id %" PRIu64, lit, reason->id);
      if (reason == d) {
        LOG ("LRAT BUILDER reason matches, unassigning lit %d", lit);
        assert (val (lit));
        assert (!unit);
        unit = lit;
      }
    }
    for (const auto &lit : simplified)
      mark (lit) = false;

    // Remove from hash table, mark as garbage, connect to garbage list.
    num_garbage++;
    assert (num_clauses);
    num_clauses--;
    *p = d->next;
    d->next = garbage;
    garbage = d;
    d->garbage = true;

    if (d->size == 1) {
      unsigned l = l2a (d->literals[0]);
      if (unit_reasons[l] == d) {
        unit_reasons[l] = 0;
      }
    }

    // we propagated unit with the deleted clause as reason. To ensure
    // topological order of the trail we have to backtrack (and repropagate)
    // usually unit should be implied by some other clause otherwise
    // deleting this clause does not really makes sense.
    //
    if (unit) {
      LOG (trail.begin (), trail.end (),
           "LRAT BUILDER propagated lits before deletion");
      while (trail.size ()) {
        int tlit = trail.back ();
        if (tlit == unit)
          break;
        unassign_reason (tlit);
        trail.pop_back ();
      }
      assert (trail.size ());
      unassign_reason (unit);
      trail.pop_back ();
    }
    if (unit || (inconsistent && inconsistent_clause->id == d->id)) {
      inconsistent_chain.clear ();
      next_to_propagate = 0;
      bool res = propagate ();
      LOG (trail.begin (), trail.end (),
           "LRAT BUILDER propagated lits after deletion");
      assert (res || inconsistent);
      if (!res) {
        inconsistent = true;
        inconsistent_clause = conflict;
      } else if (inconsistent) {
        inconsistent = false;
        inconsistent_clause = 0;
        LOG ("LRAT BUILDER no longer inconsistent after deletion of clause "
             "%" PRIu64,
             d->id);
      }
    }
  } else {
    fatal_message_start ();
    fputs ("deleted clause not in proof:\n", stderr);
    for (const auto &lit : unsimplified)
      fprintf (stderr, "%d ", lit);
    fputc ('0', stderr);
    fatal_message_end ();
  }
  clean ();
  STOP (checking);
}

/*------------------------------------------------------------------------*/

void LratBuilder::dump () {
  int max_var = 0;
  for (uint64_t i = 0; i < size_clauses; i++)
    for (LratBuilderClause *c = clauses[i]; c; c = c->next)
      for (unsigned i = 0; i < c->size; i++)
        if (abs (c->literals[i]) > max_var)
          max_var = abs (c->literals[i]);
  printf ("p cnf %d %" PRIu64 "\n", max_var, num_clauses);
  for (uint64_t i = 0; i < size_clauses; i++)
    for (LratBuilderClause *c = clauses[i]; c; c = c->next) {
      for (unsigned i = 0; i < c->size; i++)
        printf ("%d ", c->literals[i]);
      printf ("0\n");
    }
}

} // namespace CaDiCaL
