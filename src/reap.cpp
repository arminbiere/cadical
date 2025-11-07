#include "reap.hpp"
#include "util.hpp"
#include <climits>
#include <cstring>

void Reap::init () {
  for (auto &bucket : buckets)
    bucket = {0};
  Assert (!num_elements);
  Assert (!last_deleted);
  min_bucket = 32;
  Assert (!max_bucket);
}

void Reap::release () {
  num_elements = 0;
  last_deleted = 0;
  min_bucket = 32;
  max_bucket = 0;
}

Reap::Reap () {
  num_elements = 0;
  last_deleted = 0;
  min_bucket = 32;
  max_bucket = 0;
}

static inline unsigned leading_zeroes_of_unsigned (unsigned x) {
  return x ? __builtin_clz (x) : sizeof (unsigned) * 8;
}

void Reap::push (unsigned e) {
  Assert (last_deleted <= e);
  const unsigned diff = e ^ last_deleted;
  const unsigned bucket = 32 - leading_zeroes_of_unsigned (diff);
  buckets[bucket].push_back (e);
  if (min_bucket > bucket)
    min_bucket = bucket;
  if (max_bucket < bucket)
    max_bucket = bucket;
  Assert (num_elements != UINT_MAX);
  num_elements++;
}

unsigned Reap::pop () {
  Assert (num_elements > 0);
  unsigned i = min_bucket;
  for (;;) {
    Assert (i < 33);
    Assert (i <= max_bucket);
    std::vector<unsigned> &s = buckets[i];
    if (s.empty ()) {
      min_bucket = ++i;
      continue;
    }
    unsigned res;
    if (i) {
      res = UINT_MAX;
      const auto begin = std::begin (s);
      const auto end = std::end (s);
      auto q = std::begin (s);
      Assert (begin < end);
      for (auto p = begin; p != end; ++p) {
        const unsigned tmp = *p;
        if (tmp >= res)
          continue;
        res = tmp;
        q = p;
      }

      for (auto p = begin; p != end; ++p) {
        if (p == q)
          continue;
        const unsigned other = *p;
        const unsigned diff = other ^ res;
        Assert (sizeof (unsigned) == 4);
        const unsigned j = 32 - leading_zeroes_of_unsigned (diff);
        Assert (j < i);
        buckets[j].push_back (other);
        if (min_bucket > j)
          min_bucket = j;
      }

      s.clear ();

      if (i && max_bucket == i) {
#ifndef NDEBUG
        for (unsigned j = i + 1; j < 33; j++)
          Assert (buckets[j].empty ());
#endif
        if (s.empty ())
          max_bucket = i - 1;
      }
    } else {
      res = last_deleted;
      Assert (!buckets[0].empty ());
      Assert (buckets[0].at (0) == res);
      buckets[0].pop_back ();
    }

    if (min_bucket == i) {
#ifndef NDEBUG
      for (unsigned j = 0; j < i; j++)
        Assert (buckets[j].empty ());
#endif
      if (s.empty ())
        min_bucket = std::min ((int) (i + 1), 32);
    }

    --num_elements;
    Assert (last_deleted <= res);
    last_deleted = res;

    return res;
  }
}

void Reap::clear () {
  Assert (max_bucket <= 32);
  for (unsigned i = 0; i < 33; i++)
    buckets[i].clear ();
  num_elements = 0;
  last_deleted = 0;
  min_bucket = 32;
  max_bucket = 0;
}
