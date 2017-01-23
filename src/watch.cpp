#include "internal.hpp"

namespace CaDiCaL {

void Internal::init_watches () {
  assert (!wtab);
  NEW_ZERO (wtab, Watches, 2*vsize);
  assert (sizeof (Watch) == 16);
}

void Internal::reset_watches () {
  assert (wtab);
  RELEASE_DELETE (wtab, Watches, 2*vsize);
  wtab = 0;
}

// This can be quite costly since lots of memory is accessed in a rather
// random fashion, and thus we optionally profile it.

void Internal::connect_watches (bool irredundant_only) {
  START (connect);
  assert (watches ());

  LOG ("watching all %sclauses", irredundant_only ? "irredundant " : "");

  const const_clause_iterator end = clauses.end ();

  // First connect binary clauses.
  //
  for (const_clause_iterator i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (irredundant_only && c->redundant) continue;
    if (c->garbage || c->size > 2) continue;
    watch_clause (c);
  }

  // Then connect non-binary clauses.
  //
  for (const_clause_iterator i = clauses.begin (); i != end; i++) {
    Clause * c = *i;
    if (irredundant_only && c->redundant) continue;
    if (c->garbage || c->size == 2) continue;
    watch_clause (c);
  }

  STOP (connect);
}

void Internal::sort_watches () {
  assert (watches ());
  LOG ("sorting watches");
  Watches saved;
  for (int idx = 1; idx <= max_var; idx++) {
    for (int sign = -1; sign <= 1; sign += 2) {
      const int lit = sign * idx;
      Watches & ws = watches (lit);
      const_watch_iterator end = ws.end ();
      const_watch_iterator i;
      watch_iterator j = ws.begin ();
      assert (saved.empty ());
      for (i = j; i != end; i++) {
        const Watch w = *i;
        if (w.binary) *j++ = w;
        else saved.push_back (w);
      }
      ws.resize (j - ws.begin ());
      end = saved.end ();
      for (i = saved.begin (); i != end; i++)
        ws.push_back (*i);
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

};
