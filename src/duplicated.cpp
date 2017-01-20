#include "internal.hpp"

namespace CaDiCaL {

// Hyper binary resolution tends to produce too many redundant clauses if we
// do not eagerly remove duplicated binary clauses.  At the same time this
// procedure detects hyper binary units, thus in summary implements
// subsumption and strengthen for binary clauses, which complements
// 'subsume' used only to subsume and strengthen non-binary clauses.

// It also moves all the binary clauses to the front of watches.

void Internal::mark_duplicated_binary_clauses_as_garbage () {
  START (deduplicate);
  assert (!simplifying);
  assert (!level);
  assert (watches ());
  vector<int> stack;
  for (int idx = 1; !unsat && idx <= max_var; idx++) {
    if (!active (idx)) continue;
    int unit = 0;
    for (int sign = -1; !unit && sign <= 1; sign += 2) {
      const int lit = sign * idx;
      Watches & ws = watches (lit);
      const const_watch_iterator end = ws.end ();
      watch_iterator j = ws.begin ();
      const_watch_iterator i;
      assert (stack.empty ());
      for (i = j; !unit && i != end; i++) {
        Watch w = *j++ = *i;
        if (!w.binary) continue;
        int other = w.blit;
        const int tmp = marked (other);
        Clause * c = w.clause;
        if (tmp > 0) {
          LOG (c, "found duplicated");
          if (c->garbage) { j--; continue; }
          if (!c->redundant) {
            watch_iterator k;
            for (k = ws.begin ();;k++) {
              assert (k != i);
              if (!k->binary) continue;
              if (k->blit != other) continue;
              Clause * d = k->clause;
              if (d->garbage) continue;
              c = d;
              break;
            }
            *k = w;
          }
          LOG (c, "mark garbage duplicated");
          stats.subsumed++;
          stats.duplicated++;
          mark_garbage (c);
          j--;
        } else if (tmp < 0) {
          LOG ("found %d %d and %d %d which produces unit %d",
            lit, -other, lit, other, lit);
          unit = lit;
          j = ws.begin ();
        } else {
          if (c->garbage) continue;
          mark (other);
          stack.push_back (other);
        }
      }
      ws.resize (j - ws.begin ());
      while (!stack.empty ()) {
        unmark (stack.back ());
        stack.pop_back ();
      }
    }
    if (unit) {
      assign_unit (unit);
      if (!propagate ()) {
        LOG ("empty clause after propagating unit");
        learn_empty_clause ();
      }
    }
  }
  report ('2', 0);
  STOP (deduplicate);
}

};
