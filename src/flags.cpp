#include "internal.hpp"

namespace CaDiCaL {

void Internal::mark_fixed (int lit) {
  Flags & f = flags (lit);
  assert (f.status == Flags::ACTIVE);
  f.status = Flags::FIXED;
  LOG ("fixed %d", abs (lit));
  stats.all.fixed++;
  stats.now.fixed++;
  stats.inactive++;
  assert (stats.active);
  stats.active--;
  assert (!active (lit));
  assert (f.fixed ());
}

void Internal::mark_eliminated (int lit) {
  Flags & f = flags (lit);
  assert (f.status == Flags::ACTIVE);
  f.status = Flags::ELIMINATED;
  LOG ("eliminated %d", abs (lit));
  stats.all.eliminated++;
  stats.now.eliminated++;
  stats.inactive++;
  assert (stats.active);
  stats.active--;
  assert (!active (lit));
  assert (f.eliminated ());
}

void Internal::mark_pure (int lit) {
  Flags & f = flags (lit);
  assert (f.status == Flags::ACTIVE);
  f.status = Flags::PURE;
  LOG ("pure %d", abs (lit));
  stats.all.pure++;
  stats.now.pure++;
  stats.inactive++;
  assert (stats.active);
  stats.active--;
  assert (!active (lit));
  assert (f.pure ());
}

void Internal::mark_substituted (int lit) {
  Flags & f = flags (lit);
  assert (f.status == Flags::ACTIVE);
  f.status = Flags::SUBSTITUTED;
  LOG ("substituted %d", abs (lit));
  stats.all.substituted++;
  stats.now.substituted++;
  stats.inactive++;
  assert (stats.active);
  stats.active--;
  assert (!active (lit));
  assert (f.substituted ());
}

void Internal::mark_active (int lit) {
  Flags & f = flags (lit);
  assert (f.status == Flags::UNUSED);
  f.status = Flags::ACTIVE;
  LOG ("activate %d previously unused", abs (lit));
  assert (stats.inactive);
  stats.inactive--;
  assert (stats.unused);
  stats.unused--;
  stats.active++;
  assert (active (lit));
}

void Internal::reactivate (int lit) {
  assert (!active (lit));
  Flags & f = flags (lit);
  assert (f.status != Flags::FIXED);
  assert (f.status != Flags::UNUSED);
#ifdef LOGGING
  const char * msg = 0;
#endif
  switch (f.status) {
    default:
    case Flags::ELIMINATED:
      assert (f.status == Flags::ELIMINATED);
      assert (stats.now.eliminated > 0);
      stats.now.eliminated--;
#ifdef LOGGING
      msg = "eliminated";
#endif
      break;
    case Flags::SUBSTITUTED:
#ifdef LOGGING
      msg = "substituted";
#endif
      assert (stats.now.substituted > 0);
      stats.now.substituted--;
      break;
    case Flags::PURE:
#ifdef LOGGING
      msg = "pure literal";
#endif
      assert (stats.now.pure > 0);
      stats.now.pure--;
      break;
  }
#ifdef LOGGING
  assert (msg);
  LOG ("reactivate previously %s %d", msg, abs (lit));
#endif
  f.status = Flags::ACTIVE;
  assert (active (lit));
  stats.reactivated++;
  assert (stats.inactive > 0);
  stats.inactive--;
  stats.active++;
}

}
