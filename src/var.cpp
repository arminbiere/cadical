#include "internal.hpp"

namespace CaDiCaL {

void Internal::reset_subsume_bits () {
  LOG ("marking all variables as not subsume");
  for (auto idx : vars)
    flags (idx).subsume = false;
}

void Internal::check_var_stats () {
#ifndef NDEBUG
  int64_t fixed = 0, eliminated = 0, substituted = 0, pure = 0, unused = 0,
          declared = 0;
  for (auto idx : vars) {
    Flags &f = flags (idx);
    if (f.active ())
      continue;
    if (f.fixed ())
      fixed++;
    if (f.eliminated ())
      eliminated++;
    if (f.substituted ())
      substituted++;
    if (f.unused ())
      unused++;
    if (f.declared ())
      declared++;
    if (f.pure ())
      pure++;
  }
  assert (stats.vars_now_fixed == fixed);
  assert (stats.vars_now_eliminated == eliminated);
  assert (stats.vars_now_substituted == substituted);
  assert (stats.vars_now_pure == pure);
  int64_t inactive =
      unused + declared + fixed + eliminated + substituted + pure;
  assert (stats.vars_inactive == inactive);
  assert (max_var == stats.vars_active + stats.vars_inactive);
#endif
}

} // namespace CaDiCaL
