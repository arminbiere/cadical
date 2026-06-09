#include "internal.hpp"

namespace CaDiCaL {

// This initializes variables on the binary 'scores' heap also with
// smallest variable index first (thus picked first) and larger indices at
// the end.
//
void Internal::init_scores (int old_max_var, int new_max_var) {
  LOG ("initializing EVSIDS scores from %d to %d", old_max_var + 1,
       new_max_var);
  for (int i = old_max_var; i < new_max_var; i++)
    scores.push_back (i + 1);
}

double Internal::get_vsids_score (int var) {
  assert (var > 0);
  const unsigned idx = abs (var);
  if (stab.size () <= idx)
    return 0;
  return stab[idx];
}

// Shuffle the EVSIDS heap.

void Internal::shuffle_scores () {
  if (!opts.shuffle)
    return;
  if (!opts.shufflescores)
    return;
  assert (!level);
  stats.scores_shuffled++;
  LOG ("shuffling scores");
  vector<int> shuffle;
  if (opts.shufflerandom) {
    scores.erase ();
    for (int idx = max_var; idx; idx--)
      if (!flags (idx).unused ())
        shuffle.push_back (idx);
    Random random (opts.seed);       // global seed
    random += stats.scores_shuffled; // different every time
    const int size_activated = shuffle.size ();
    for (int i = 0; i <= size_activated - 2; i++) {
      const int j = random.pick_int (i, size_activated - 1);
      swap (shuffle[i], shuffle[j]);
    }
  } else {
    while (!scores.empty ()) {
      int idx = scores.front ();
      (void) scores.pop_front ();
      shuffle.push_back (idx);
    }
  }
  score_inc = 0;
  for (const auto &idx : shuffle) {
    stab[idx] = score_inc++;
    scores.push_back (idx);
  }
}

} // namespace CaDiCaL
