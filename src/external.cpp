#include "internal.hpp"

namespace CaDiCaL {

External::External (Internal * i)
:
  vsize (0),
  max_var (0),
  vals (0),
  solution (0),
  e2i (0),
  internal (i)
{
  assert (internal);
  assert (!internal->external);
  internal->external = this;
}

External::~External () {
  if (vals) DELETE_ONLY (vals, signed_char, vsize);
  if (solution) DELETE_ONLY (solution, signed_char, vsize);
  if (e2i) DELETE_ONLY (e2i, int, vsize);
}

void External::enlarge (int new_max_var) {
  size_t new_vsize = vsize ? 2*vsize : 1 + (size_t) new_max_var;
  while (new_vsize <= (size_t) new_max_var) new_vsize *= 2;
  LOG ("enlarge external from size %ld to new size %ld", vsize, new_vsize);
  ENLARGE_ONLY (vals, signed_char, vsize, new_vsize);
  ENLARGE_ONLY (e2i, int, vsize, new_vsize);
  vsize = new_vsize;
}

void External::init (int new_max_var) {
  if (new_max_var <= max_var) return;
  int new_vars = new_max_var - max_var;
  int old_internal_max_var = internal->max_var;
  int new_internal_max_var = old_internal_max_var + new_vars;
  internal->init (new_internal_max_var);
  if ((size_t) new_max_var >= vsize) enlarge (new_max_var);
  for (int i = max_var + 1; i <= new_max_var;  i++) vals[i] = -1;
  LOG ("initialized %d external variables", new_vars);
  int eidx = max_var + 1, iidx = old_internal_max_var + 1;
  for (int i = max_var + 1; i <= new_max_var; i++) {
    LOG ("mapping external %d to internal %d", eidx, iidx);
    e2i[eidx] = iidx, internal->i2e[iidx] = eidx;
    eidx++, iidx++;
  }
  assert (iidx == new_internal_max_var + 1);
  assert (eidx == new_max_var + 1);
  max_var = new_max_var;
}

void External::add (int elit) {
  if (internal->opts.check) original.push_back (elit);
  const int ilit = internalize (elit);
  assert (!elit || ilit);
  if (elit) LOG ("adding external %d as internal %d", elit, ilit);
  internal->add_original_lit (ilit);
}

int External::solve () {
  int res = internal->solve ();
  if (res == 10) {
    extend ();
    if (internal->opts.check) check (&External::val);
  }
  return res;
}

};
