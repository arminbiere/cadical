#include "internal.hpp"
#include <vector>

namespace CaDiCaL {

// Slightly different than 'bump_variable' since the variable is not
// enqueued at all.

void Internal::init_enqueue (int idx) {
  Link &l = links[idx];
  assert (flags (idx).active () || flags (idx).fixed ());
  if (opts.varprioritizeswap) {
    LOG ("enqueueing %s at the beginning", LOGLIT (idx));
    l.prev = 0;
    if (queue.first) {
      assert (!links[queue.first].prev);
      links[queue.first].prev = idx;
      btab[idx] = btab[queue.first] - 1;
    } else {
      assert (!queue.last);
      queue.last = idx;
      btab[idx] = 0;
    }
    assert (btab[idx] <= stats.vars_bumped);
    l.next = queue.first;
    queue.first = idx;
    LOG ("enqueueing %s at the beginning, next: %d, last: %d", LOGLIT (idx),
         l.next, queue.last);
    // due to interactions with IPASIR-UP, we need to update it every time.
    // if (!queue.unassigned)
    update_queue_unassigned (queue.last);
  } else {
    LOG ("enqueueing %s at the end", LOGLIT (idx));
    l.next = 0;
    if (queue.last) {
      assert (!links[queue.last].next);
      links[queue.last].next = idx;
    } else {
      assert (!queue.first);
      queue.first = idx;
    }
    btab[idx] = ++stats.vars_bumped;
    l.prev = queue.last;
    queue.last = idx;
    update_queue_unassigned (queue.last);
  }
}

// Initialize VMTF queue from current 'old_max_var + 1' to 'new_max_var'.
// This incorporates an initial variable order.  We currently simply assume
// that variables with smaller index are more important.  This is the same
// as in MiniSAT (implicitly) and also matches the 'scores' initialization.
//
void Internal::init_queue (int old_max_var, int new_max_var) {
  LOG ("initializing VMTF queue from %d to %d", old_max_var + 1,
       new_max_var);
  assert (old_max_var < new_max_var);
  // New variables can be created that can invoke enlarge anytime (eg via
  // calls during ipasir-up call-backs), thus assuming (!level) is not
  // correct
  for (int idx = old_max_var; idx < new_max_var; idx++)
    init_enqueue (idx + 1);
}

double Internal::get_vmtf_score (int var) {
  assert (var > 0);
  const unsigned idx = abs (var);
  if (btab.size () <= idx)
    return 0;
  return btab[idx];
}

// Shuffle the VMTF queue.

void Internal::shuffle_queue () {
  if (!opts.shuffle)
    return;
  if (!opts.shufflequeue)
    return;
  stats.scores_shuffled++;
  LOG ("shuffling queue");
  vector<int> shuffle;
  if (opts.shufflerandom) {
    for (int idx = max_var; idx; idx--)
      if (!flags (idx).unused ())
        shuffle.push_back (idx);
    Random random (opts.seed);       // global seed
    random += stats.scores_shuffled; // different every time
    const int highest_var = shuffle.size ();
    for (int i = 0; i <= highest_var - 2; i++) {
      const int j = random.pick_int (i, highest_var - 1);
      swap (shuffle[i], shuffle[j]);
    }
  } else {
    for (int idx = queue.last; idx; idx = links[idx].prev)
      shuffle.push_back (idx);
  }
  queue.first = queue.last = 0;
  for (const int idx : shuffle)
    queue.enqueue (links, idx);
  int64_t bumped = queue.bumped;
  for (int idx = queue.last; idx; idx = links[idx].prev)
    btab[idx] = bumped--;
  queue.unassigned = queue.last;
}

void Internal::check_queue () {
#ifndef NDEBUG
  int res = queue.first;
  std::vector<bool> seen;
  seen.resize (max_var + 1, false);
  while (res) {
    assert (!flags (res).declared () && !flags (res).unused ());
    seen[res] = true;
    int next = links[res].next;
    if (!next)
      break;
    assert (links[next].prev == res);
    assert (btab[next] > btab[res]);
    res = next;
  }

  res = queue.last;
  while (res != queue.unassigned) {
    assert (!flags (res).declared () && !flags (res).unused ());
    assert (internal->val (res));
    res = links[res].prev;
    assert (res);
  }

  for (auto v : vars) {
    if (!active (v))
      continue;
    assert (seen[v]);
  }
#endif
}

} // namespace CaDiCaL
