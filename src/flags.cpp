#include "internal.hpp"

namespace CaDiCaL {

void Internal::mark_fixed (int lit) {
  if (external->fixed_listener) {
    int elit = externalize (lit);
    Assert (elit);
    const int eidx = abs (elit);
    if (!external->ervars[eidx])
      external->fixed_listener->notify_fixed_assignment (elit);
  }
  Flags &f = flags (lit);
  Assert (f.status == Flags::ACTIVE);
  f.status = Flags::FIXED;
  LOG ("fixed %d", abs (lit));
  stats.all.fixed++;
  stats.now.fixed++;
  stats.inactive++;
  Assert (stats.active);
  stats.active--;
  Assert (!active (lit));
  Assert (f.fixed ());

  if (external_prop && private_steps) {
    // If pre/inprocessing found a fixed assignment, we want the propagator
    // to know about it.
    // But at that point it is not guaranteed to be already on the trail, so
    // notification will happen only later.
    Assert (!level || in_mode (BACKBONE));
  }
}

void Internal::mark_eliminated (int lit) {
  Flags &f = flags (lit);
  Assert (f.status == Flags::ACTIVE);
  f.status = Flags::ELIMINATED;
  LOG ("eliminated %d", abs (lit));
  stats.all.eliminated++;
  stats.now.eliminated++;
  stats.inactive++;
  Assert (stats.active);
  stats.active--;
  Assert (!active (lit));
  Assert (f.eliminated ());
}

void Internal::mark_pure (int lit) {
  Flags &f = flags (lit);
  Assert (f.status == Flags::ACTIVE);
  f.status = Flags::PURE;
  LOG ("pure %d", abs (lit));
  stats.all.pure++;
  stats.now.pure++;
  stats.inactive++;
  Assert (stats.active);
  stats.active--;
  Assert (!active (lit));
  Assert (f.pure ());
}

void Internal::mark_substituted (int lit) {
  Flags &f = flags (lit);
  Assert (f.status == Flags::ACTIVE);
  f.status = Flags::SUBSTITUTED;
  LOG ("substituted %d", abs (lit));
  stats.all.substituted++;
  stats.now.substituted++;
  stats.inactive++;
  Assert (stats.active);
  stats.active--;
  Assert (!active (lit));
  Assert (f.substituted ());
}

void Internal::mark_active (int lit) {
  Flags &f = flags (lit);
  Assert (f.status == Flags::UNUSED);
  f.status = Flags::ACTIVE;
  LOG ("activate %d previously unused", abs (lit));
  Assert (stats.inactive);
  stats.inactive--;
  Assert (stats.unused);
  stats.unused--;
  stats.active++;
  Assert (active (lit));
}

void Internal::reactivate (int lit) {
  Assert (!active (lit));
  Flags &f = flags (lit);
  Assert (f.status != Flags::FIXED);
  Assert (f.status != Flags::UNUSED);
#ifdef LOGGING
  const char *msg = 0;
#endif
  switch (f.status) {
  default:
  case Flags::ELIMINATED:
    Assert (f.status == Flags::ELIMINATED);
    Assert (stats.now.eliminated > 0);
    stats.now.eliminated--;
#ifdef LOGGING
    msg = "eliminated";
#endif
    break;
  case Flags::SUBSTITUTED:
#ifdef LOGGING
    msg = "substituted";
#endif
    Assert (stats.now.substituted > 0);
    stats.now.substituted--;
    break;
  case Flags::PURE:
#ifdef LOGGING
    msg = "pure literal";
#endif
    Assert (stats.now.pure > 0);
    stats.now.pure--;
    break;
  }
#ifdef LOGGING
  Assert (msg);
  LOG ("reactivate previously %s %d", msg, abs (lit));
#endif
  f.status = Flags::ACTIVE;
  f.sweep = false;
  Assert (active (lit));
  stats.reactivated++;
  Assert (stats.inactive > 0);
  stats.inactive--;
  stats.active++;
}

} // namespace CaDiCaL
