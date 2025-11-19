#include "walk.hpp"
#include "internal.hpp"
#include "random.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Random walk local search based on 'ProbSAT' ideas.

// We (based on the Master project from Leah Hohl) tried to ticks
// local search similarly to the other parts of the solver with
// limited success however.
//
// On the problem `ncc_none_5047_6_3_3_3_0_435991723', the broken part
// of walk_flip is very cheap and should not be counted in ticks, but
// on various other problems `9pipe_k' it is very important to ticks
// this part too.

//  using ClauseOrBinary = std::variant <Clause*, TaggedBinary>;

struct Walker {

  Internal *internal;

  // for efficiency, storing the model each time an improvement is
  // found is too costly. Instead we store some of the flips since
  // last time and the position of the best model found so far.
  Random random;                 // local random number generator
  int64_t ticks;                 // ticks to approximate run time
  int64_t limit;                 // limit on number of propagations
  vector<ClauseOrBinary> broken; // currently unsatisfied clauses
  double epsilon;                // smallest considered score
  vector<double> table;          // break value to score table
  vector<double> scores;         // scores of candidate literals
  std::vector<int>
      flips; // remember the flips compared to the last best saved model
  int best_trail_pos;
  int64_t minimum = INT64_MAX;
  std::vector<signed char> best_values; // best model stored so far
  double score (unsigned);              // compute score from break count
#ifndef NDEBUG
  std::vector<signed char> current_best_model; // best model found so far
#endif
  Walker (Internal *, int64_t limit);
  void populate_table (double size);
  void push_flipped (int flipped);
  void save_walker_trail (bool);
  void save_final_minimum (int64_t old_minimum);
};

// These are in essence the CB values from Adrian Balint's thesis.  They
// denote the inverse 'cb' of the base 'b' of the (probability) weight
// 'b^-i' for picking a literal with the break value 'i' (first column is
// the 'size', second the 'CB' value).

static double cbvals[][2] = {
    {0.0, 2.00}, {3.0, 2.50}, {4.0, 2.85}, {5.0, 3.70},
    {6.0, 5.10}, {7.0, 7.40}, // Adrian has '5.4', but '7.4' looks better.
};

static const int ncbvals = sizeof cbvals / sizeof cbvals[0];

// We interpolate the CB values for uniform random SAT formula to the non
// integer situation of average clause size by piecewise linear functions.
//
//   y2 - y1
//   ------- * (x - x1) + y1
//   x2 - x1
//
// where 'x' is the average size of clauses and 'y' the CB value.

inline static double fitcbval (double size) {
  int i = 0;
  while (i + 2 < ncbvals &&
         (cbvals[i][0] > size || cbvals[i + 1][0] < size))
    i++;
  const double x2 = cbvals[i + 1][0], x1 = cbvals[i][0];
  const double y2 = cbvals[i + 1][1], y1 = cbvals[i][1];
  const double dx = x2 - x1, dy = y2 - y1;
  assert (dx);
  const double res = dy * (size - x1) / dx + y1;
  assert (res > 0);
  return res;
}

// Initialize the data structures for one local search round.

Walker::Walker (Internal *i, int64_t l)
    : internal (i), random (internal->opts.seed), // global random seed
      ticks (0), limit (l), best_trail_pos (-1) {
  random += internal->stats.walk.count; // different seed every time
  flips.reserve (i->max_var / 4);
  best_values.resize (i->max_var + 1, 0);
#ifndef NDEBUG
  current_best_model.resize (i->max_var + 1, 0);
#endif
}

void Walker::populate_table (double size) {
  // This is the magic constant in ProbSAT (also called 'CB'), which we pick
  // according to the average size every second invocation and otherwise
  // just the default '2.0', which turns into the base '0.5'.
  //
  const bool use_size_based_cb = (internal->stats.walk.count & 1);
  const double cb = use_size_based_cb ? fitcbval (size) : 2.0;
  assert (cb);
  const double base = 1 / cb; // scores are 'base^0,base^1,base^2,...

  double next = 1;
  for (epsilon = next; next; next = epsilon * base)
    table.push_back (epsilon = next);

  PHASE ("walk", internal->stats.walk.count,
         "CB %.2f with inverse %.2f as base and table size %zd", cb, base,
         table.size ());
}

// Add the literal to flip to the queue

void Walker::push_flipped (int flipped) {
  LOG ("push literal %s on the flips", LOGLIT (flipped));
  assert (flipped);
  if (best_trail_pos < 0) {
    LOG ("not pushing flipped %s to already invalid trail",
         LOGLIT (flipped));
    return;
  }

  const size_t size_trail = flips.size ();
  const size_t limit = internal->max_var / 4 + 1;
  if (size_trail < limit) {
    flips.push_back (flipped);
    LOG ("pushed flipped %s to trail which now has size %zd",
         LOGLIT (flipped), size_trail + 1);
    return;
  }

  if (best_trail_pos) {
    LOG ("trail reached limit %zd but has best position %d", limit,
         best_trail_pos);
    save_walker_trail (true);
    flips.push_back (flipped);
    LOG ("pushed flipped %s to trail which now has size %zu",
         LOGLIT (flipped), flips.size ());
    return;
  } else {
    LOG ("trail reached limit %zd without best position", limit);
    flips.clear ();
    LOG ("not pushing %s to invalidated trail", LOGLIT (flipped));
    best_trail_pos = -1;
    LOG ("best trail position becomes invalid");
  }
}

void Walker::save_walker_trail (bool keep) {
  assert (best_trail_pos != -1);
  assert ((size_t) best_trail_pos <= flips.size ());
//  assert (!keep || best_trail_pos == flips.size());
#ifdef LOGGING
  const size_t size_trail = flips.size ();
#endif
  const int kept = flips.size () - best_trail_pos;
  LOG ("saving %d values of flipped literals on trail of size %zd",
       best_trail_pos, flips.size ());

  const auto begin = flips.begin ();
  const auto best = flips.begin () + best_trail_pos;
  const auto end = flips.end ();

  auto it = begin;
  for (; it != best; ++it) {
    const int lit = *it;
    assert (lit);
    const signed char value = sign (lit);
    const int idx = std::abs (lit);
    best_values[idx] = value;
  }
  if (!keep) {
    LOG ("no need to shift and keep remaining %u literals", kept);
    return;
  }

#ifndef NDEBUG
  for (auto v : internal->vars) {
    if (internal->active (v))
      assert (best_values[v] == current_best_model[v]);
  }
#endif
  LOG ("flushed %u literals %.0f%% from trail", best_trail_pos,
       percent (best_trail_pos, size_trail));
  assert (it == best);
  auto jt = begin;
  for (; it != end; ++it, ++jt) {
    assert (jt <= it);
    assert (it < end);
    *jt = *it;
  }

  assert ((int) (end - jt) == best_trail_pos);
  assert ((int) (jt - begin) == kept);
  flips.resize (kept);
  LOG ("keeping %u literals %.0f%% on trail", kept,
       percent (kept, size_trail));
  LOG ("reset best trail position to 0");
  best_trail_pos = 0;
}

// finally export the final minimum
void Walker::save_final_minimum (int64_t old_init_minimum) {
  assert (minimum <= old_init_minimum);
#ifdef NDEBUG
  (void) old_init_minimum;
#endif

  if (!best_trail_pos || best_trail_pos == -1)
    LOG ("minimum already saved");
  else
    save_walker_trail (false);

  ++internal->stats.walk.improved;
  for (auto v : internal->vars) {
    if (best_values[v])
      internal->phases.saved[v] = best_values[v];
    else
      assert (!internal->active (v));
  }
  internal->copy_phases (internal->phases.prev);
}
// The scores are tabulated for faster computation (to avoid 'pow').

inline double Walker::score (unsigned i) {
  const double res = (i < table.size () ? table[i] : epsilon);
  LOG ("break %u mapped to score %g", i, res);
  return res;
}

/*------------------------------------------------------------------------*/

ClauseOrBinary Internal::walk_pick_clause (Walker &walker) {
  require_mode (WALK);
  assert (!walker.broken.empty ());
  int64_t size = walker.broken.size ();
  if (size > INT_MAX)
    size = INT_MAX;
  int pos = walker.random.pick_int (0, size - 1);
  ClauseOrBinary res = walker.broken[pos];
#ifdef LOGGING
  Clause *c;
  if (!res.is_binary ())
    c = res.clause ();
  else
    c = res.tagged_binary ().d;
  LOG (c, "picking random position %d", pos);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

// Compute the number of clauses which would be become unsatisfied if 'lit'
// is flipped and set to false.  This is called the 'break-count' of 'lit'.

unsigned Internal::walk_break_value (int lit, int64_t &ticks) {
  require_mode (WALK);
  START (walkbreak);
  assert (val (lit) > 0);
  const int64_t oldticks = ticks;

  unsigned res = 0; // The computed break-count of 'lit'.
  ticks += (1 + cache_lines (watches (lit).size (), sizeof (Clause *)));

  for (auto &w : watches (lit)) {
    assert (w.blit != lit);
    if (val (w.blit) > 0)
      continue;
    if (w.binary ()) {
      res++;
      continue;
    }

    Clause *c = w.clause;
#ifdef LOGGING
    assert (c != dummy_binary);
#endif
    ++ticks;

    assert (lit == c->literals[0]);

    // Now try to find a second satisfied literal starting at 'literals[1]'
    // shifting all the traversed literals to right by one position in order
    // to move such a second satisfying literal to 'literals[1]'.  This move
    // to front strategy improves the chances to find the second satisfying
    // literal earlier in subsequent break-count computations.
    //
    auto begin = c->begin () + 1;
    const auto end = c->end ();
    auto i = begin;
    int prev = 0;
    while (i != end) {
      const int other = *i;
      *i++ = prev;
      prev = other;
      if (val (other) < 0)
        continue;

      // Found 'other' as second satisfying literal.

      w.blit = other; // Update 'blit'
      *begin = other; // and move to front.

      break;
    }

    if (i != end)
      continue; // Double satisfied!

    // Otherwise restore literals (undo shift to the right).
    //
    while (i != begin) {
      const int other = *--i;
      *i = prev;
      prev = other;
    }
    res++; // Literal 'lit' single satisfies clause 'c'.
  }
  stats.ticks.walkbreak += (ticks - oldticks);
  STOP (walkbreak);

  return res;
}

/*------------------------------------------------------------------------*/

// Given an unsatisfied clause 'c', in which we want to flip a literal, we
// first determine the exponential score based on the break-count of its
// literals and then sample the literals based on these scores.  The CB
// value is smaller than one and thus the score is exponentially decreasing
// with the break-count increasing.  The sampling works as in 'ProbSAT' and
// 'YalSAT' by summing up the scores and then picking a random limit in the
// range of zero to the sum, then summing up the scores again and picking
// the first literal which reaches the limit.  Note, that during incremental
// SAT solving we can not flip assumed variables.  Those are assigned at
// decision level one, while the other variables are assigned at two.

int Internal::walk_pick_lit (Walker &walker, Clause *c) {
  LOG ("picking literal by break-count");
  assert (walker.scores.empty ());
  const int64_t old = walker.ticks;
  walker.ticks += 1;
  double sum = 0;
  int64_t propagations = 0;
  for (const auto lit : *c) {
    assert (active (lit));
    if (var (lit).level == 1) {
      LOG ("skipping assumption %d for scoring", -lit);
      continue;
    }
    assert (active (lit));
    propagations++;
    unsigned tmp = walk_break_value (-lit, walker.ticks);
    double score = walker.score (tmp);
    LOG ("literal %d break-count %u score %g", lit, tmp, score);
    walker.scores.push_back (score);
    sum += score;
  }
  (void) propagations; // TODO actually unused?
  LOG ("scored %zd literals", walker.scores.size ());
  assert (!walker.scores.empty ());
  assert (walker.scores.size () <= (size_t) c->size);
  const double lim = sum * walker.random.generate_double ();
  LOG ("score sum %g limit %g", sum, lim);
  const auto end = c->end ();
  auto i = c->begin ();
  auto j = walker.scores.begin ();
  int res;
  for (;;) {
    assert (i != end);
    res = *i++;
    if (var (res).level > 1)
      break;
    LOG ("skipping assumption %d without score", -res);
  }
  sum = *j++;
  while (sum <= lim && i != end) {
    res = *i++;
    if (var (res).level == 1) {
      LOG ("skipping assumption %d without score", -res);
      continue;
    }
    sum += *j++;
  }
  walker.scores.clear ();
  LOG ("picking literal %d by break-count", res);
  stats.ticks.walkpick += walker.ticks - old;
  return res;
}

int Internal::walk_pick_lit (Walker &walker, ClauseOrBinary c) {
  if (c.is_binary ())
    return walk_pick_lit (walker, c.tagged_binary ());
  return walk_pick_lit (walker, c.clause ());
}

int Internal::walk_pick_lit (Walker &walker, const TaggedBinary c) {
  LOG ("picking literal by break-count on binary clause [%" PRIu64 "]%s %s",
       c.d->id, LOGLIT (c.lit), LOGLIT (c.other));
  assert (walker.scores.empty ());
  const int64_t old = walker.ticks;
  double sum = 0;
  int64_t propagations = 0;
  const std::array<int, 2> clause = {c.lit, c.other};
  for (const auto lit : clause) {
    assert (active (lit));
    if (var (lit).level == 1) {
      LOG ("skipping assumption %d for scoring", -lit);
      continue;
    }
    assert (active (lit));
    assert (val (lit) < 0);
    propagations++;
    unsigned tmp = walk_break_value (-lit, walker.ticks);
    double score = walker.score (tmp);
    LOG ("literal %d break-count %u score %g", lit, tmp, score);
    walker.scores.push_back (score);
    sum += score;
  }
  (void) propagations; // TODO unused?
  LOG ("scored %zd literals", walker.scores.size ());
  assert (!walker.scores.empty ());
  assert (walker.scores.size () <= (size_t) 2);
  const double lim = sum * walker.random.generate_double ();
  LOG ("score sum %g limit %g", sum, lim);
  const auto end = clause.end ();
  auto i = clause.begin ();
  auto j = walker.scores.begin ();
  int res = 0;
  for (;;) {
    assert (i != end);
    res = *i++;
    if (var (res).level > 1)
      break;
    LOG ("skipping assumption %d without score", -res);
  }
  sum = *j++;
  while (sum <= lim && i != end) {
    res = *i++;
    if (var (res).level == 1) {
      LOG ("skipping assumption %d without score", -res);
      continue;
    }
    sum += *j++;
  }
  assert (res);
  walker.scores.clear ();
  LOG ("picking literal %d by break-count", res);
  stats.ticks.walkpick += walker.ticks - old;
  return res;
}

/*------------------------------------------------------------------------*/

// flips a literal unless we run out of ticks.
bool Internal::walk_flip_lit (Walker &walker, int lit) {
  START (walkflip);
  const int64_t old = walker.ticks;
  require_mode (WALK);
  LOG ("flipping assign %d", lit);
  assert (val (lit) < 0);

  // First flip the literal value.
  //
  const int tmp = sign (lit);
  const int idx = abs (lit);
  set_val (idx, tmp);
  assert (val (lit) > 0);

  // we are going to need it anyway and it probably still is in memory
  const Watches &ws = watches (-lit);
  if (!ws.empty ()) {
    const Watch &w = ws[0];
    __builtin_prefetch (&w, 0, 1);
  }

  // Then remove 'c' and all other now satisfied (made) clauses.
  {
    // Simply go over all unsatisfied (broken) clauses.

    LOG ("trying to make %zd broken clauses", walker.broken.size ());

    const auto eou = walker.broken.end ();
    // broken is in cache given how central it is... but not always (see the
    // ncc problems). Value was heuristically determined to give reasonnable
    // values.
    walker.ticks +=
        1 + cache_lines (walker.broken.size (), sizeof (Clause *));
    auto j = walker.broken.begin (), i = j;
#if defined(LOGGING) || !defined(NDEBUG)
    int64_t made = 0;
#endif

    while (i != eou) {

      ClauseOrBinary tagged = *j++ = *i++;

      if (tagged.is_binary ()) {
        const TaggedBinary &b = tagged.tagged_binary ();
        const int clit = b.lit;
        const int other = b.other;
        assert (val (clit) < 0 || val (other) < 0);
#if defined(LOGGING)
        assert (b.d->literals[0] == clit || b.d->literals[1] == clit);
        assert (b.d->literals[0] == other || b.d->literals[1] == other);
#endif
        if (clit == lit || other == lit) {
          LOG (b.d, "made");
          const int first_lit = lit;
          const int second_lit = clit ^ lit ^ other;
#ifdef LOGGING
          watch_binary_literal (first_lit, second_lit, b.d);
#else
          // placeholder for the clause, does not matter
          watch_binary_literal (first_lit, second_lit, dummy_binary);
#endif

          ++walker.ticks;
#if defined(LOGGING) || !defined(NDEBUG)
          made++;
#endif
          j--;
        } else {
          LOG (b.d, "still broken");
          assert (val (clit) < 0 && val (other) < 0);
        }
        continue;
      }

      // now the expansive part
      Clause *d = tagged.clause ();
      ++walker.ticks;
      int *literals = d->literals;
      LOG (d, "search for replacement");
      int prev = 0;
      // Find 'lit' in 'd'.
      //
      const int size = d->size;
      for (int i = 0; i < size; i++) {
        const int other = literals[i];
        assert (active (other));
        literals[i] = prev;
        prev = other;
        if (other == lit)
          break;
        assert (val (other) < 0);
      }
      // If 'lit' is in 'd' then move it to the front to watch it.
      //
      if (prev == lit) {
        literals[0] = lit;
        LOG (d, "made");
        watch_literal (literals[0], literals[1], d);
        ++walker.ticks;
#if defined(LOGGING) || !defined(NDEBUG)
        made++;
#endif
        j--;
      } else { // Otherwise the clause is not satisfied, undo shift.

        for (int i = size - 1; i >= 0; i--) {
          int other = literals[i];
          literals[i] = prev;
          prev = other;
        }
      }
      LOG (d, "clause after undoing shift");
    }
    assert ((int64_t) (j - walker.broken.begin ()) + made ==
            (int64_t) walker.broken.size ());
    walker.broken.resize (j - walker.broken.begin ());
    LOG ("made %" PRId64 " clauses by flipping %d, still %zu broken", made,
         lit, walker.broken.size ());
#ifndef NDEBUG
    for (auto d : walker.broken) {
      if (d.is_binary ()) {
        const TaggedBinary &b = d.tagged_binary ();
        assert (val (b.lit) < 0 && val (b.other) < 0);
      } else {
        for (auto lit : *d.clause ())
          assert (val (lit) < 0);
      }
    }
#endif
    if (walker.ticks > walker.limit) {
      STOP (walkflip);
      return false;
    }
  }

  stats.ticks.walkflipbroken += walker.ticks - old;

  const int64_t old_after_broken = walker.ticks;

  // Finally add all new unsatisfied (broken) clauses.
  {
#ifdef LOGGING
    int64_t broken = 0;
#endif
    Watches &ws = watches (-lit);
    // probably still in cache
    walker.ticks += 1 + cache_lines (ws.size (), sizeof (Clause *));

    LOG ("trying to break %zd watched clauses", ws.size ());

    for (const auto &w : ws) {
      Clause *d = w.clause;
      const bool binary = w.binary ();
      if (binary) {
        const int other = w.blit;
        assert (w.blit != -lit);
        if (val (other) > 0) {
          LOG (d, "unwatch %d in", -lit);
          watch_binary_literal (other, -lit, d);
          ++walker.ticks;
          continue;
        }
        LOG (d, "broken");
#ifdef LOGGING
        assert (d != dummy_binary);
#endif
        walker.broken.push_back (TaggedBinary (d, -lit, other));
        ++walker.ticks;
#ifdef LOGGING
        broken++;
#endif
        continue;
      }

      if (walker.ticks > walker.limit) {
        STOP (walkflip);
        return false;
      }
      // now the expansive part
      assert (d->size != 2);
      ++walker.ticks;
      int *literals = d->literals, replacement = 0, prev = -lit;
      assert (d->size == w.size);
      const int size = d->size;
      assert (literals[0] == -lit);

      for (int i = 1; i < size; i++) {
        const int other = literals[i];
        assert (active (other));
        literals[i] = prev; // shift all to right
        prev = other;
        const signed char tmp = val (other);
        if (tmp < 0)
          continue;
        replacement = other; // satisfying literal
        break;
      }
      if (replacement) {
        assert (-lit != replacement);
        literals[1] = -lit;
        literals[0] = replacement;
        watch_literal (replacement, -lit, d);
        ++walker.ticks;
        LOG (d, "found replacement");
      } else {
        for (int i = size - 1; i > 0; i--) { // undo shift
          const int other = literals[i];
          literals[i] = prev;
          prev = other;
        }

        assert (literals[0] == -lit);
        LOG (d, "broken");
        walker.broken.push_back (d);
        ++walker.ticks;
#ifdef LOGGING
        broken++;
#endif
      }
    }
    LOG ("broken %" PRId64 " clauses by flipping %d", broken, lit);
    ws.clear ();
  }
  STOP (walkflip);
  stats.ticks.walkflipWL += walker.ticks - old_after_broken;
  stats.ticks.walkflip += walker.ticks - old;
  return true;
}

/*------------------------------------------------------------------------*/

// Check whether to save the current phases as new global minimum.

inline void Internal::walk_save_minimum (Walker &walker) {
  int64_t broken = walker.broken.size ();
  if (broken >= walker.minimum)
    return;
  if (broken <= stats.walk.minimum) {
    stats.walk.minimum = broken;
    VERBOSE (3, "new global minimum %" PRId64 "", broken);
  } else {
    VERBOSE (3, "new walk minimum %" PRId64 "", broken);
  }

  walker.minimum = broken;

#ifndef NDEBUG
  for (auto i : vars) {
    const signed char tmp = vals[i];
    if (tmp)
      walker.current_best_model[i] = tmp;
  }
  if (walker.minimum == 0) {
    for (auto c : clauses) {
      if (c->garbage)
        continue;
      if (c->redundant)
        continue;
      int satisfied = 0;
      for (const auto &lit : *c) {
        const int tmp = internal->val (lit);
        if (tmp > 0) {
          LOG (c, "satisfied literal %d in", lit);
          satisfied++;
        }
      }
      assert (satisfied);
    }
  }
#endif
  if (walker.best_trail_pos == -1) {
    VERBOSE (3, "saving the new walk minimum %" PRId64 "", broken);
    for (auto i : vars) {
      const signed char tmp = vals[i];
      if (tmp) {
        walker.best_values[i] = tmp;
#ifndef NDEBUG
        assert (tmp == walker.current_best_model[i]);
#endif
      } else {
        assert (!active (i));
      }
    }
    walker.best_trail_pos = 0;
  } else {
    walker.best_trail_pos = walker.flips.size ();
    LOG ("new best trail position %u", walker.best_trail_pos);
  }
}

/*------------------------------------------------------------------------*/

int Internal::walk_round (int64_t limit, bool prev) {

  stats.walk.count++;

  clear_watches ();

  // Remove all fixed variables first (assigned at decision level zero).
  //
  if (last.collect.fixed < stats.all.fixed)
    garbage_collection ();

#ifndef QUIET
  // We want to see more messages during initial local search.
  //
  if (localsearching) {
    assert (!force_phase_messages);
    force_phase_messages = true;
  }
#endif

  PHASE ("walk", stats.walk.count, "random walk limit of %" PRId64 " ticks",
         limit);

  // Instantiate data structures for this local search round.
  //
  Walker walker (internal, limit);
#ifndef QUIET
  int old_global_minimum = stats.walk.minimum;
#endif

  bool failed = false; // Inconsistent assumptions?

  level = 1; // Assumed variables assigned at level 1.

  if (assumptions.empty ()) {
    LOG ("no assumptions so assigning all variables to decision phase");
  } else {
    LOG ("assigning assumptions to their forced phase first");
    for (const auto lit : assumptions) {
      signed char tmp = val (lit);
      if (tmp > 0)
        continue;
      if (tmp < 0) {
        LOG ("inconsistent assumption %d", lit);
        failed = true;
        break;
      }
      if (!active (lit))
        continue;
      tmp = sign (lit);
      const int idx = abs (lit);
      LOG ("initial assign %d to assumption phase", tmp < 0 ? -idx : idx);
      set_val (idx, tmp);
      assert (level == 1);
      var (idx).level = 1;
    }
    if (!failed)
      LOG ("now assigning remaining variables to their decision phase");
  }

  level = 2; // All other non assumed variables assigned at level 2.

  if (!failed) {

    // warmup stores the result in phases, not in target
    const bool target = opts.warmup ? false : stable || opts.target == 2;
    for (auto idx : vars) {
      if (!active (idx)) {
        LOG ("skipping inactive variable %d", idx);
        continue;
      }
      if (vals[idx]) {
        assert (var (idx).level == 1);
        LOG ("skipping assumed variable %d", idx);
        continue;
      }
      int tmp = 0;
      if (prev)
        tmp = phases.prev[idx];
      if (!tmp)
        tmp = sign (decide_phase (idx, target));
      assert (tmp == 1 || tmp == -1);
      set_val (idx, tmp);
      assert (level == 2);
      var (idx).level = 2;
      LOG ("initial assign %d to decision phase", tmp < 0 ? -idx : idx);
    }

    LOG ("watching satisfied and registering broken clauses");
#ifdef LOGGING
    int64_t watched = 0;
#endif

    double size = 0;
    int64_t n = 0;
    for (const auto c : clauses) {

      if (c->garbage)
        continue;
      if (c->redundant) {
        if (!opts.walkredundant)
          continue;
        if (!likely_to_be_kept_clause (c))
          continue;
      }

      bool satisfiable = false; // contains not only assumptions
      int satisfied = 0;        // clause satisfied?

      int *lits = c->literals;
      size += c->size;
      n++;
      const int size = c->size;

      // Move to front satisfied literals and determine whether there
      // is at least one (non-assumed) literal that can be flipped.
      //
      for (int i = 0; satisfied < 2 && i < size; i++) {
        const int lit = lits[i];
        assert (active (lit)); // Due to garbage collection.
        if (val (lit) > 0) {
          swap (lits[satisfied], lits[i]);
          if (!satisfied++)
            LOG ("first satisfying literal %d", lit);
        } else if (!satisfiable && var (lit).level > 1) {
          LOG ("non-assumption potentially satisfying literal %d", lit);
          satisfiable = true;
        }
      }

      if (!satisfied && !satisfiable) {
        LOG (c, "due to assumptions unsatisfiable");
        LOG ("stopping local search since assumptions falsify a clause");
        failed = true;
        break;
      }

      if (satisfied) {
        LOG (c, "pushing to satisfied");
        if (c->size == 2)
          watch_binary_literal (lits[0], lits[1], c);
        else
          watch_literal (lits[0], lits[1], c);
#ifdef LOGGING
        watched++;
#endif
      } else {
        assert (satisfiable); // at least one non-assumed variable ...
        LOG (c, "broken");
        assert (c->size == size);
        if (size == 2)
          walker.broken.push_back (TaggedBinary (c));
        else
          walker.broken.push_back (c);
      }
    }

    double average_size = relative (size, n);
    walker.populate_table (average_size);
    PHASE ("walk", stats.walk.count,
           "%" PRId64 " clauses average size %.2f over %d variables", n,
           average_size, active ());

#ifdef LOGGING
    if (!failed) {
      int64_t broken = walker.broken.size ();
      int64_t total = watched + broken;
      LOG ("watching %" PRId64 " clauses %.0f%% "
           "out of %" PRId64 " (watched and broken)",
           watched, percent (watched, total), total);
    }
#endif
  }

  assert (failed || walker.table.size ());

  int res; // Tells caller to continue with local search.

  if (!failed) {

    int64_t broken = walker.broken.size ();
    int64_t initial_minimum = broken;

    PHASE ("walk", stats.walk.count,
           "starting with %" PRId64 " unsatisfied clauses "
           "(%.0f%% out of %" PRId64 ")",
           broken, percent (broken, stats.current.irredundant),
           stats.current.irredundant);

    walk_save_minimum (walker);
    assert (stats.walk.minimum <= walker.minimum);

    int64_t minimum = broken;
#ifndef QUIET
    int64_t flips = 0;
#endif
    while (!terminated_asynchronously () && !walker.broken.empty () &&
           walker.ticks < walker.limit) {
#ifndef QUIET
      flips++;
#endif
      stats.walk.flips++;
      stats.walk.broken += broken;
      ClauseOrBinary c = walk_pick_clause (walker);
      const int lit = walk_pick_lit (walker, c);
      bool finished = walk_flip_lit (walker, lit);
      if (!finished)
        break;
      walker.push_flipped (lit);
      broken = walker.broken.size ();
      LOG ("now have %" PRId64 " broken clauses in total", broken);
      if (broken >= minimum)
        continue;
      minimum = broken;
      VERBOSE (3, "new phase minimum %" PRId64 " after %" PRId64 " flips",
               minimum, flips);
      walk_save_minimum (walker);
    }

    walker.save_final_minimum (initial_minimum);

#ifndef QUIET
    if (minimum == initial_minimum) {
      PHASE ("walk", internal->stats.walk.count,
             "%sno improvement %" PRId64 "%s in %" PRId64 " flips and "
             "%" PRId64 " ticks",
             tout.bright_yellow_code (), minimum, tout.normal_code (),
             flips, walker.ticks);
    } else if (minimum < old_global_minimum)
      PHASE ("walk", stats.walk.count,
             "%snew global minimum %" PRId64 "%s in %" PRId64 " flips and "
             "%" PRId64 " ticks",
             tout.bright_yellow_code (), minimum, tout.normal_code (),
             flips, walker.ticks);
    else
      PHASE ("walk", stats.walk.count,
             "best phase minimum %" PRId64 " in %" PRId64 " flips and "
             "%" PRId64 " ticks",
             minimum, flips, walker.ticks);

    if (opts.profile >= 2) {
      PHASE ("walk", stats.walk.count, "%.2f million ticks per second",
             1e-6 *
                 relative (walker.ticks, time () - profiles.walk.started));

      PHASE ("walk", stats.walk.count, "%.2f thousand flips per second",
             relative (1e-3 * flips, time () - profiles.walk.started));

    } else {
      PHASE ("walk", stats.walk.count, "%.2f ticks", 1e-6 * walker.ticks);

      PHASE ("walk", stats.walk.count, "%.2f thousand flips", 1e-3 * flips);
    }
#endif

    if (minimum > 0) {
      LOG ("minimum %" PRId64 " non-zero thus potentially continue",
           minimum);
      res = 0;
    } else {
      LOG ("minimum is zero thus stop local search");
      res = 10;
    }

  } else {

    res = 20;

    PHASE ("walk", stats.walk.count,
           "aborted due to inconsistent assumptions");
  }

  for (auto idx : vars)
    if (active (idx))
      set_val (idx, 0);

  assert (level == 2);
  level = 0;

  clear_watches ();
  connect_watches ();

#ifndef QUIET
  if (localsearching) {
    assert (force_phase_messages);
    force_phase_messages = false;
  }
#endif
  stats.ticks.walk += walker.ticks;
  return res;
}

void Internal::walk () {
  START_INNER_WALK ();

  backtrack ();
  if (propagated < trail.size () && !propagate ()) {
    LOG ("empty clause after root level propagation");
    learn_empty_clause ();
    STOP_INNER_WALK ();
    return;
  }

  int res = 0;
  if (opts.warmup)
    res = warmup ();
  if (res) {
    LOG ("stopping walk due to warmup");
    STOP_INNER_WALK ();
    return;
  }
  const int64_t ticks = stats.ticks.search[0] + stats.ticks.search[1];
  int64_t limit = ticks - last.walk.ticks;
  VERBOSE (2,
           "walk scheduling: last %" PRId64 " current %" PRId64
           " delta %" PRId64,
           last.walk.ticks, ticks, limit);
  last.walk.ticks = ticks;
  limit *= 1e-3 * opts.walkeffort;
  if (limit < opts.walkmineff)
    limit = opts.walkmineff;
  // local search is very cache friendly, so we actually really go over a
  // lot of ticks
  if (limit > 1e3 * opts.walkmaxeff) {
    MSG ("reached maximum efficiency %" PRId64, limit);
    limit = 1e3 * opts.walkmaxeff;
  }
  (void) walk_round (limit, false);
  STOP_INNER_WALK ();
  assert (!unsat);
}

} // namespace CaDiCaL
