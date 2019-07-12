#include "internal.hpp"

namespace CaDiCaL {

void Internal::init_watches () {
  assert (wtab.empty ());
  while (wtab.size () < 2*vsize)
    wtab.push_back (Watches ());
  LOG ("initialized watcher tables");
}

void Internal::clear_watches () {
  for (int idx = 1; idx <= max_var; idx++)
    for (int sign = -1; sign <= 1; sign += 2)
      watches (sign * idx).clear ();
}

void Internal::reset_watches () {
  assert (!wtab.empty ());
  erase_vector (wtab);
  LOG ("reset watcher tables");
}

// This can be quite costly since lots of memory is accessed in a rather
// random fashion, and thus we optionally profile it.

void Internal::connect_watches (bool irredundant_only) {
  START (connect);
  assert (watching ());

  LOG ("watching all %sclauses", irredundant_only ? "irredundant " : "");

  // First connect binary clauses.
  //
  for (const auto & c : clauses) {
    if (irredundant_only && c->redundant) continue;
    if (c->garbage || c->size > 2) continue;
    watch_clause (c);
  }

  // Then connect non-binary clauses.
  //
  for (const auto & c : clauses) {
    if (irredundant_only && c->redundant) continue;
    if (c->garbage || c->size == 2) continue;
    watch_clause (c);
    if (!level) {
      int lit0 = c->literals[0];
      int lit1 = c->literals[1];
      int tmp0 = val (lit0);
      int tmp1 = val (lit1);
      if (tmp0 > 0) continue;
      if (tmp1 > 0) continue;
      if (tmp0 < 0) {
        const size_t pos0 = var (lit0).trail;
        if (pos0 < propagated) {
          propagated = pos0;
          LOG ("literal %d resets propagated to %zd", lit0, pos0);
        }
      }
      if (tmp1 < 0) {
        const size_t pos1 = var (lit1).trail;
        if (pos1 < propagated) {
          propagated = pos1;
          LOG ("literal %d resets propagated to %zd", lit1, pos1);
        }
      }
    }
  }

  STOP (connect);
}

void Internal::sort_watches () {
  assert (watching ());
  LOG ("sorting watches");
  Watches saved;
  for (int idx = 1; idx <= max_var; idx++) {
    for (int sign = -1; sign <= 1; sign += 2) {

      const int lit = sign * idx;
      Watches & ws = watches (lit);

      const const_watch_iterator end = ws.end ();
      watch_iterator j = ws.begin ();
      const_watch_iterator i;

      assert (saved.empty ());

      for (i = j; i != end; i++) {
        const Watch w = *i;
        if (w.binary ()) *j++ = w;
        else saved.push_back (w);
      }
      ws.resize (j - ws.begin ());

      for (const auto & w : saved)
        ws.push_back (w);

      saved.clear ();
    }
  }
}

void Internal::disconnect_watches () {
  LOG ("disconnecting watches");
  for (int idx = 1; idx <= max_var; idx++)
    for (int sign = -1; sign <= 1; sign += 2)
      watches (sign * idx).clear ();
}

}
