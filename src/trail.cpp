#include "internal.hpp"

namespace CaDiCaL {

// adds a trail to trails and the control to multitrail
//
void Internal::new_trail_level (int lit) {
  level++;
  control.push_back (Level (lit, trail.size ()));
  if (!opts.reimply)
    return;
  assert (multitrail_dirty == level - 1);
  multitrail_dirty++;
  multitrail.push_back (0);
  control.back ().trail = notify_trail.size ();
  size_t reserving = 0;
  if (level < 50)
    reserving = max_var / 10;
  if (reserving > 50)
    reserving = 50;
  vector<int> a;
  trails.push_back (a);
  trails.back ().reserve (reserving);
  assert ((trails.back ()).size () == 0);
  assert (level == (int) trails.size ());
}

// clears all trails above level
//
void Internal::clear_trails (int level) {
  assert (level >= 0);
  trails.resize (level);
}

// returns size of trail
// with opts.reimply returns size of trail of level l
//
int Internal::trail_size (int l) {
  if (!opts.reimply || l == 0)
    return (int) trail.size ();
  assert (l > 0 && trails.size () >= (size_t) l);
  return (int) trails[l - 1].size ();
}

// returns the trail that needs to be propagated
//
vector<int> *Internal::next_trail (int l) {
  if (!opts.reimply || l <= 0) {
    return &trail;
  }
  assert (l > 0 && trails.size () >= (size_t) l);
  return &trails[l - 1];
}

// returns the point from which the trail is propagated
//
int Internal::next_propagated (int l) {
  if (l < 0)
    return 0;
  if (!opts.reimply || l == 0) {
    return propagated;
  }
  assert (l > 0 && trails.size () >= (size_t) l);
  return multitrail[l - 1];
}

// returns the lowest level within some conflicting clause
//
int Internal::conflicting_level (Clause *c) {
  int l = 0;
  for (const auto &lit : *c) {
    const int ll = var (lit).level;
    l = l < ll ? ll : l;
  }
  return l;
}

// updates propagated for the current level
//
void Internal::set_propagated (int l, int prop) {
  if (!opts.reimply || l == 0) {
    propagated = prop;
    return;
  }
  multitrail[l - 1] = prop;
}

} // namespace CaDiCaL
