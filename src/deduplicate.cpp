#include "internal.hpp"

namespace CaDiCaL {

// Equivalent literal substitution in 'decompose' and shrinking in 'subsume'
// or 'vivify' might produce duplicated binary clauses.  They can not be
// found in 'subsume' nor 'vivify' since we explicitly do not consider
// binary clauses as candidates to be shrunken or subsumed.  They are
// detected here by a simple scan of watch lists and then marked as garbage.
// This is actually also quite fast.

// Further it might also be possible that two binary clauses can be resolved
// to produce a unit (we call it 'hyper unary resolution').  For example
// resolving the binary clauses '1 -2' and '1 2' produces the unit '1'.
// This could be found by probing in 'probe' unless '-1' also occurs in a
// binary clause (add the clause '-1 2' to those two clauses) in which case
// '1' as well as '2' both occur positively as well as negatively and none
// of them nor their negation is considered as probe

void Internal::mark_duplicated_binary_clauses_as_garbage () {

  if (!opts.deduplicate)
    return;
  if (unsat)
    return;
  if (terminated_asynchronously ())
    return;

  START_SIMPLIFIER (deduplicate, DEDUP);
  stats.deduplications++;

  assert (!level);
  assert (watching ());

  vector<int> stack; // To save marked literals and unmark them later.

  int64_t subsumed = 0;
  int64_t units = 0;

  for (auto idx : vars) {

    if (unsat)
      break;
    if (!active (idx))
      continue;
    int unit = 0;

    for (int sign = -1; !unit && sign <= 1; sign += 2) {

      const int lit = sign * idx; // Consider all literals.

      assert (stack.empty ());
      Watches &ws = watches (lit);

      // We are removing references to garbage clause. Thus no 'auto'.

      const const_watch_iterator end = ws.end ();
      watch_iterator j = ws.begin ();
      const_watch_iterator i;

      for (i = j; !unit && i != end; i++) {
        Watch w = *j++ = *i;
        if (!w.binary ())
          continue;
        int other = w.blit;
        const int tmp = marked (other);
        Clause *c = w.clause;

        if (tmp > 0) { // Found duplicated binary clause.

          if (c->garbage) {
            j--;
            continue;
          }
          LOG (c, "found duplicated");

          // The previous identical clause 'd' might be redundant and if the
          // second clause 'c' is not (so irredundant), then we have to keep
          // 'c' instead of 'd', thus we search for it and replace it.

          if (!c->redundant) {
            watch_iterator k;
            for (k = ws.begin ();; k++) {
              assert (k != i);
              if (!k->binary ())
                continue;
              if (k->blit != other)
                continue;
              Clause *d = k->clause;
              if (d->garbage)
                continue;
              c = d;
              break;
            }
            *k = w;
          }

          LOG (c, "mark garbage duplicated");
          stats.subsumed++;
          stats.deduplicated++;
          subsumed++;
          mark_garbage (c);
          j--;

        } else if (tmp < 0) { // Hyper unary resolution.

          LOG ("found %d %d and %d %d which produces unit %d", lit, -other,
               lit, other, lit);
          unit = lit;
          if (lrat) {
            // taken from fradical
            assert (lrat_chain.empty ());
            lrat_chain.push_back (c->id);
            // We've forgotten where the other binary clause is, so go find
            // it again
            for (watch_iterator k = ws.begin ();; k++) {
              assert (k != i);
              if (!k->binary ())
                continue;
              if (k->blit != -other)
                continue;
              lrat_chain.push_back (k->clause->id);
              break;
            }
          }
          j = ws.begin (); // Flush 'ws'.
          units++;

        } else {
          if (c->garbage)
            continue;
          mark (other);
          stack.push_back (other);
        }
      }

      if (j == ws.begin ())
        erase_vector (ws);
      else if (j != end)
        ws.resize (j - ws.begin ()); // Shrink watchers.

      for (const auto &other : stack)
        unmark (other);

      stack.clear ();
    }

    // Propagation potentially messes up the watches and thus we can not
    // propagate the unit immediately after finding it.  Instead we break
    // out of both loops and assign and propagate the unit here.

    if (unit) {

      stats.failed++;
      stats.hyperunary++;
      assign_unit (unit);
      // lrat_chain.clear ();   done in search_assign

      if (!propagate ()) {
        LOG ("empty clause after propagating unit");
        learn_empty_clause ();
      }
    }
  }
  STOP_SIMPLIFIER (deduplicate, DEDUP);

  report ('2', !opts.reportall && !(subsumed + units));
}

/*------------------------------------------------------------------------*/

// See the comment for vivifyflush.
//
struct deduplicate_flush_smaller {

  bool operator() (Clause *a, Clause *b) const {

    const auto eoa = a->end (), eob = b->end ();
    auto i = a->begin (), j = b->begin ();
    for (; i != eoa && j != eob; i++, j++)
      if (*i != *j)
        return *i < *j;
    const bool smaller = j == eob && i != eoa;
    return smaller;
  }
};


/*------------------------------------------------------------------------*/

// We discovered in a bug report
// (https://github.com/arminbiere/cadical/issues/147) that some problems
// contains clauses several times. This was handled properly before (as a side
// effect of vivifyflush), but the proper ticks scheduling limitation makes this
// impossible since 2.2. Therefore, we have implemented this detection as a
// proper inprocessing technique that is off by default and run only once during
// preprocess quickly. As we do not want to assume anything on the input
// clauses, we also remove the true/false literals.
//
// In essence, the code is simply taken from vivifyflush (without all the rest
// of the code around obviously).
//
void Internal::deduplicate_all_clauses () {
  assert (!level);
  reset_watches ();

  mark_satisfied_clauses_as_garbage ();
  garbage_collection ();

  // in order to do the inprocessing inplace, we remove the deleted clauses, put
  // the binary deleted clauses first. Then we work on the non-deleted clauses
  // by sorting them and sorting the clause w.r.t each other.
  clauses.end () = std::remove_if (clauses.begin (), clauses.end(), [](Clause *c){return c->garbage && c->size !=2;});
  auto start = std::partition (clauses.begin (), clauses.end (), [](Clause *c) {return c->garbage;});
  const auto end = clauses.end ();
  std::for_each (start, end, [](Clause *c) {return sort (c->begin(), c->end ());});

  stable_sort (start, clauses.end (), deduplicate_flush_smaller ());
  auto j = start, i = j;

  Clause *prev = 0;
  int64_t subsumed = 0;
  for (; i != end; i++) {
    Clause *c = *j++ = *i;
    if (!prev || c->size < prev->size) {
      prev = c;
      continue;
    }
    const auto eop = prev->end ();
    auto k = prev->begin ();
    for (auto l = c->begin (); k != eop; k++, l++)
      if (*k != *l)
        break;
    if (k == eop) {
      LOG (c, "found subsumed");
      LOG (prev, "subsuming");
      assert (!c->garbage);
      assert (!prev->garbage);
      assert (c->redundant || !prev->redundant);
      mark_garbage (c);
      subsumed++;
      j--;
    } else
      prev = c;
  }

  if (subsumed) {
    clauses.resize (j - clauses.begin ());
  } else
    assert (j == end);

  ++stats.deduplicatedinitrounds;
  PHASE ("deduplicate-all", stats.deduplicatedinitrounds,
      "flushed %" PRId64 " subsumed clauses out of %zd", subsumed, clauses.end () - start);
  stats.subsumed += subsumed;
  stats.deduplicatedinit += subsumed;

  init_watches();
  connect_watches();
  report ('d', !opts.reportall && !subsumed);
}
} // namespace CaDiCaL
