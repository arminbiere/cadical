#include "flags.hpp"
#include "internal.hpp"

namespace CaDiCaL {

void Internal::mark_declared (int lit) {
  Flags &f = flags (lit);
  assert (f.status == Flags::UNUSED);
  f.status = Flags::DECLARED;
  ++stats.vars_declared;
  --stats.vars_unused;
  LOG ("declaring new %d (max_var: %d, unused: %" PRId64
       ", active: %" PRId64 ")",
       lit, max_var, stats.vars_unused, stats.vars_active);
}

void Internal::mark_fixed (int lit) {
  if (external->fixed_listener) {
    int elit = externalize (lit);
    assert (elit);
    const int eidx = abs (elit);
    if (!external->ervars[eidx])
      external->fixed_listener->notify_fixed_assignment (elit);
  }
  Flags &f = flags (lit);
  if (f.status == Flags::DECLARED)
    mark_active (lit);
  assert (f.status == Flags::ACTIVE);
  f.status = Flags::FIXED;
  LOG ("fixed %d", abs (lit));
  stats.vars_all_fixed++;
  stats.vars_now_fixed++;
  stats.vars_inactive++;
  assert (stats.vars_active);
  stats.vars_active--;
  assert (!active (lit));
  assert (f.fixed ());

  if (external_prop && private_steps) {
    // If pre/inprocessing found a fixed assignment, we want the propagator
    // to know about it.
    // But at that point it is not guaranteed to be already on the trail, so
    // notification will happen only later.
    assert (!level || in_mode (BACKBONE));
  }
}

void Internal::mark_eliminated (int lit) {
  Flags &f = flags (lit);
  assert (f.status == Flags::ACTIVE);
  f.status = Flags::ELIMINATED;
  LOG ("eliminated %d", abs (lit));
  if (f.factored)
    stats.factored_eliminated++;
  stats.vars_all_elim++;
  stats.vars_now_eliminated++;
  stats.vars_inactive++;
  assert (stats.vars_active);
  stats.vars_active--;
  assert (!active (lit));
  assert (f.eliminated ());
}

void Internal::mark_pure (int lit) {
  Flags &f = flags (lit);
  assert (f.status == Flags::ACTIVE);
  f.status = Flags::PURE;
  LOG ("pure %d", abs (lit));
  stats.vars_all_pure++;
  stats.vars_now_pure++;
  stats.vars_inactive++;
  assert (stats.vars_active);
  stats.vars_active--;
  assert (!active (lit));
  assert (f.pure ());
}

void Internal::mark_substituted (int lit) {
  Flags &f = flags (lit);
  assert (f.status == Flags::ACTIVE);
  f.status = Flags::SUBSTITUTED;
  LOG ("substituted %d", abs (lit));
  stats.vars_all_substituted++;
  stats.vars_now_substituted++;
  stats.vars_inactive++;
  assert (stats.vars_active);
  stats.vars_active--;
  assert (!active (lit));
  assert (f.substituted ());
}

void Internal::mark_active (int lit) {
  Flags &f = flags (lit);
  assert (f.status == Flags::DECLARED);
  f.status = Flags::ACTIVE;
  LOG ("activate %d previously declared", abs (lit));
  assert (stats.vars_inactive);
  stats.vars_inactive--;
  assert (stats.vars_declared);
  stats.vars_declared--;
  stats.vars_active++;
  assert (active (lit));
}

void Internal::reactivate (int lit) {
  assert (!active (lit));
  Flags &f = flags (lit);
  assert (f.status != Flags::FIXED);
  assert (f.status != Flags::UNUSED);
#ifdef LOGGING
  const char *msg = 0;
#endif
  switch (f.status) {
  default:
  case Flags::ELIMINATED:
    assert (f.status == Flags::ELIMINATED);
    assert (stats.vars_now_eliminated > 0);
    stats.vars_now_eliminated--;
#ifdef LOGGING
    msg = "eliminated";
#endif
    break;
  case Flags::SUBSTITUTED:
#ifdef LOGGING
    msg = "substituted";
#endif
    assert (stats.vars_now_substituted > 0);
    stats.vars_now_substituted--;
    break;
  case Flags::PURE:
#ifdef LOGGING
    msg = "pure literal";
#endif
    assert (stats.vars_now_pure > 0);
    stats.vars_now_pure--;
    break;
  }
#ifdef LOGGING
  assert (msg);
  LOG ("reactivate previously %s %d", msg, abs (lit));
#endif
  f.status = Flags::ACTIVE;
  f.sweep = false;
  assert (active (lit));
  stats.vars_reactivated++;
  assert (stats.vars_inactive > 0);
  stats.vars_inactive--;
  stats.vars_active++;
}

} // namespace CaDiCaL
