#include "internal.hpp"
#include "reap.hpp"

namespace CaDiCaL {

  void Internal::reset_shrinkable()
  {
    size_t reset = 0;
    for(const auto & lit : shrinkable) {
      LOG("resetting lit %i", lit);
      Flags &f = flags(lit);
      assert(f.shrinkable);
      f.shrinkable = false;
      ++reset;
    }
    LOG("resetting %zu shrinkable variables", reset);
  }

  void Internal::mark_shrinkable_as_removable(int blevel, std::vector<int>::size_type minimized_start) {
    size_t marked = 0, reset = 0;
#ifndef NDEBUG
    unsigned kept = 0, minireset = 0;
    for(; minimized_start < minimized.size(); ++minimized_start) {
      const int lit = minimized[minimized_start];
      Flags &f = flags(lit);
      const Var &v = var(lit);
      if (v.level == blevel) {
        assert(!f.poison);
        ++minireset;
      }
      else ++kept;
    }
#else
    (void) blevel;
    (void) minimized_start;
#endif


    for (const int lit : shrinkable) {
      Flags &f = flags(lit);
      assert(f.shrinkable);
      assert(!f.poison);
      f.shrinkable = false;
      ++reset;
      if(f.removable)
        continue;
      f.removable = true;
      minimized.push_back(lit);
      ++marked;
    }
    LOG("resetting %zu shrinkable variables", reset);
    LOG("marked %zu removable variables", marked);
  }

  int inline Internal::shrink_literal(int lit, int blevel, unsigned max_trail)
  {
    assert(val(lit) < 0);

    Flags &f = flags(lit);
    const Var &v = var(lit);
    assert(v.level <= blevel);

    if(!v.level) {
      LOG("skipping root level assigned %d", (lit));
      return 0;
    }
    if (f.shrinkable) {
      LOG("skipping already shrinkable literal %d", (lit));
      return 0;
    }

    if (v.level < blevel) {
      if (f.removable) {
        LOG("skipping removable thus shrinkable %d", (lit));
        return 0;
      }
      const bool always_minimize_on_lower_blevel = (opts.shrink > 2);
      if (always_minimize_on_lower_blevel &&
          minimize_literal(-lit, 1)) {
        LOG("minimized thus shrinkable %d", (lit));
        return 0;
      }
      LOG("literal %d on lower blevel %u < %u not removable/shrinkable",
          (lit), v.level, blevel);
      return -1;
    }

    LOG("marking %d as shrinkable", lit);
    f.shrinkable = true;
    f.poison = false;
    shrinkable.push_back(lit);
    if (opts.shrinkreap) {
      assert (max_trail < trail.size());
      const unsigned dist = max_trail - v.trail;
      reap.push(dist);
    }
    return 1;
  }

  unsigned Internal::shrunken_block_uip(
      int uip, int blevel, std::vector<int>::reverse_iterator &rbegin_block,
      std::vector<int>::reverse_iterator &rend_block,
      std::vector<int>::size_type minimized_start, const int uip0)
  {
    assert(clause[0] == uip0);

    LOG("UIP on level %u, uip: %i (replacing by %i)", blevel, uip, uip0);
    assert(rend_block > rbegin_block);
    assert(rend_block < clause.rend());
    unsigned block_shrunken = 0;
    *rbegin_block = -uip;
    Var &v = var(-uip);
    Level &l = control[v.level];
    l.seen.trail = v.trail;
    l.seen.count = 1;

    Flags &f = flags(-uip);
    if(!f.seen) {
      analyzed.push_back(-uip);
      f.seen = true;
    }

    flags(-uip).keep = true;
    for (auto p = rbegin_block + 1; p != rend_block; ++p) 
      {
        const int lit = *p;
        if (lit == -uip0) continue;
        *p = uip0;
        // if (lit == -uip) continue;
        ++block_shrunken;
        assert(clause[0] == uip0);
      }
    mark_shrinkable_as_removable(blevel, minimized_start);
    assert(clause[0] == uip0);
    return block_shrunken;
  }

  void inline Internal::shrunken_block_no_uip(
                                              const std::vector<int>::reverse_iterator &rbegin_block,
                                              const std::vector<int>::reverse_iterator &rend_block,
                                              unsigned &block_minimized,
                                              const int uip0) {
    STOP(shrink);
    START(minimize);
    assert(rend_block > rbegin_block);
    LOG("no UIP found, now minimizing");
    for (auto p = rbegin_block; p != rend_block; ++p) {
      assert(p != clause.rend() - 1);
      const int lit = *p;
      if (opts.minimize && minimize_literal(-lit)) {
        assert(!flags(lit).keep);
        ++block_minimized;
        *p = uip0;
      } else {
        flags(lit).keep = true;
        assert(flags(lit).keep);
      }
    }
    STOP(minimize);
    START(shrink);
  }

  void Internal::push_literals_of_block(const std::vector<int>::reverse_iterator &rbegin_block,
                                        const std::vector<int>::reverse_iterator &rend_block,
                                        int blevel, unsigned max_trail)
  {
    assert(rbegin_block < rend_block);
    for(auto p = rbegin_block; p != rend_block; ++p) {
      assert(p != clause.rend() - 1);
      assert(!flags(*p).keep);
      const int lit = *p;
      LOG("pushing lit %i of blevel %i", lit, var(lit).level);
#ifndef NDEBUG
      int tmp =
#endif
        shrink_literal(lit, blevel, max_trail);
      assert(tmp > 0);
    }
  }

  unsigned inline Internal::shrink_next(unsigned &open, unsigned& max_trail)
  {
    if(opts.shrinkreap) {
      assert(!reap.empty());
      const unsigned dist = reap.pop();
      --open;
      assert (dist <= max_trail);
      const unsigned pos = max_trail - dist;
      assert(pos < trail.size());
      const int uip = trail[pos];
      assert(val(uip) > 0);
      LOG("trying to shrink literal %d at trail[%u]", uip, pos);
      return uip;
    } else {
      int uip;
#ifndef NDEBUG
      unsigned init_max_trail = max_trail;
#endif
      do {
        assert(max_trail <= init_max_trail);
        uip = trail[max_trail--];
      } while (!flags (uip).shrinkable);
      --open;
      LOG("open is now %d, uip = %d", open, uip);
      return uip;
    }
  }

  unsigned inline Internal::shrink_along_reason(int uip, int blevel, bool resolve_large_clauses, bool &failed_ptr, unsigned max_trail)
  {
    LOG("shrinking along the reason of lit %i", uip);
    unsigned open = 0;
 #ifndef NDEBUG
    const Flags&f = flags(uip);
#endif
    const Var&v = var(uip);

    assert(f.shrinkable);
    assert(v.level == blevel);
    assert(v.reason);

    if (resolve_large_clauses || v.reason->size == 2)
      {
        const Clause &c = *v.reason;
        LOG(v.reason, "resolving with reason");
        for(int lit : c) {
          if(lit == uip)
            continue;
          assert(val(lit) < 0);
          int tmp = shrink_literal(lit, blevel, max_trail);
          if(tmp < 0) {
            failed_ptr = true;
            break;
          }
          if(tmp > 0) {
            ++open;
          }
        }
      }
    else {
      failed_ptr = true;
    }
    return open;
  }

  unsigned Internal::shrink_block(std::vector<int>::reverse_iterator &rbegin_lits,
                                  std::vector<int>::reverse_iterator &rend_block,
                                  int blevel,
                                  unsigned &open,
                                  unsigned & block_minimized,
                                  const int uip0,
                                  unsigned max_trail)
  {
    assert(shrinkable.empty());
    assert(blevel <= this->level);
    assert(open < clause.size());
    assert(rbegin_lits >= clause.rbegin());
    assert(rend_block < clause.rend());
    assert(rbegin_lits < rend_block);

    LOG("trying to shrink %u literals on level %u", open, blevel);
    LOG("maximum trail position %zd on level %u", trail.size(), blevel);
    if (opts.shrinkreap)
      LOG ("shrinking up to %u", max_trail);

    const bool resolve_large_clauses = (opts.shrink > 2);
    bool failed = (opts.shrink == 0);
    unsigned block_shrunken = 0;
    std::vector<int>::size_type minimized_start = minimized.size();
    int uip = uip0;
    unsigned max_trail2 = max_trail;

    if(!failed) {
      push_literals_of_block(rbegin_lits, rend_block, blevel, max_trail);
      assert(!opts.shrinkreap || reap.size() == open);

      assert(open > 0);
      while (!failed) {
        assert(!opts.shrinkreap || reap.size() == open);
        uip = shrink_next(open, max_trail);
        if(open == 0) {
          break;
        }
        open += shrink_along_reason(uip, blevel, resolve_large_clauses, failed, max_trail2);
        assert(open >= 1);
      }

      if(!failed)
        LOG("shrinking found UIP %i on level %i (open: %d)", uip, blevel, open);
      else
        LOG("shrinking failed on level %i", blevel);
    }

    if(failed)
      reset_shrinkable(), shrunken_block_no_uip(rbegin_lits, rend_block, block_minimized, uip0);
    else
      block_shrunken = shrunken_block_uip(uip, blevel, rbegin_lits, rend_block, minimized_start, uip0);

    if(opts.shrinkreap)
      reap.clear();
    shrinkable.clear();
    return block_shrunken;
  }

  // Smaller level and trail.  Comparing literals on their level is necessary
  // for chronological backtracking, since trail order might in this case not
  // respect level order.

  struct shrink_trail_negative_rank {
    Internal *internal;
    shrink_trail_negative_rank(Internal *s) : internal(s) {}
    typedef uint64_t Type;
    Type operator()(int a) {
      Var &v = internal->var(a);
      uint64_t res = v.level;
      res <<= 32;
      res |= v.trail;
      return ~res;
    }
  };

  struct shrink_trail_larger {
    Internal *internal;
    shrink_trail_larger(Internal *s) : internal(s) {}
    bool operator()(const int &a, const int &b) const {
      return shrink_trail_negative_rank(internal)(a) <
             shrink_trail_negative_rank(internal)(b);
    }
  };

  // Finds the beginning of the block (rend_block, non-included) ending at rend_block (included).
  // Then tries to shrinks and minimizes literals  the block
  std::vector<int>::reverse_iterator Internal::minimize_and_shrink_block(
          std::vector<int>::reverse_iterator &rbegin_block, unsigned &total_shrunken,
          unsigned &total_minimized,
          const int uip0)

  {
    LOG("shrinking block");
    assert(rbegin_block < clause.rend() -1);
    int blevel;
    unsigned open = 0;
    unsigned max_trail;
 
    // find begining of block;
    std::vector<int>::reverse_iterator rend_block;
    {
      assert(rbegin_block <= clause.rend());
      const int lit = *rbegin_block;
      const int idx = vidx (lit);
      blevel = vtab[idx].level;
      max_trail = vtab[idx].trail;
      LOG("Block at level %i (first lit: %i)", blevel, lit);


      rend_block = rbegin_block;
      bool finished;
      do {
        assert(rend_block < clause.rend() - 1);
        const int lit = *(++rend_block);
        const int idx = vidx (lit);
        finished = (blevel != vtab[idx].level);
        if(!finished && (unsigned)vtab[idx].trail > max_trail)
          max_trail = vtab[idx].trail;
        ++ open;
        LOG("testing if lit %i is on the same level (of lit: %i, global: %i)", lit, vtab[idx].level, blevel);

      } while(!finished);

    }
    assert(open > 0);
    assert(open < clause.size());
    assert(rbegin_block < clause.rend());
    assert(rend_block < clause.rend());

    unsigned block_shrunken = 0, block_minimized = 0;
    if (open < 2) {
        flags(*rbegin_block).keep = true;
        minimized.push_back(*rbegin_block);
    }
    else
      block_shrunken = shrink_block(rbegin_block, rend_block, blevel, open, block_minimized, uip0, max_trail);

    LOG("shrunken %u literals on level %u (including %u minimized)",
        block_shrunken, blevel, block_minimized);

    total_shrunken += block_shrunken;
    total_minimized += block_minimized;

    return rend_block;
  }

  void Internal::shrink_and_minimize_clause() {
    assert(opts.minimize || opts.shrink > 0);
    LOG(clause, "shrink first UIP clause");

    START(shrink);
    external->check_learned_clause(); // check 1st UIP learned clause first
    MSORT(opts.radixsortlim, clause.begin(), clause.end(),
          shrink_trail_negative_rank(this), shrink_trail_larger(this));
    unsigned total_shrunken = 0;
    unsigned total_minimized = 0;

    LOG(clause, "shrink first UIP clause (asserting lit: %i)", clause[0]);

    auto rend_lits = clause.rend() -1;
    auto rend_block = clause.rbegin();
    const int uip0 = clause[0];

    while (rend_block != rend_lits) {
      rend_block = minimize_and_shrink_block(rend_block,
                                             total_shrunken, total_minimized, uip0);
    }

    LOG(clause, "post shrink pass (with uips, not removed) first UIP clause");
#if defined(LOGGING) || !defined(NDEBUG)
    const unsigned old_size = clause.size();
#endif
    {
      std::vector<int>::size_type i = 1;
      for (std::vector<int>::size_type j = 1; j < clause.size(); ++j) {
        assert(i <= j);
        clause[i] = clause[j];
        if (clause[j] == uip0)
          continue;
        assert(flags(clause[i]).keep);
        ++i;
        LOG("keeping literal %i", clause[j]);
      }
      clause.resize(i);
    }
    assert(old_size == (unsigned)clause.size() + total_shrunken + total_minimized);
    LOG(clause, "after shrinking first UIP clause");
    LOG("clause shrunken by %zd literals (including %u minimized)", old_size - clause.size(),
        total_minimized);

    stats.shrunken += total_shrunken;
    stats.minishrunken += total_minimized;
    STOP(shrink);

    START(minimize);
    clear_minimized_literals();
    STOP(minimize);
  }

} // namespace CaDiCaL
