#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

FratTracer::FratTracer (Internal *i, File *f, bool b, bool a)
    : internal (i), file (f), binary (b), with_antecedents (a), added (0),
      deleted (0)
#ifndef QUIET
      ,
      finalized (0), original (0)
#endif
{
  (void) internal;
}

void FratTracer::connect_internal (Internal *i) {
  internal = i;
  file->connect_internal (internal);
  LOG ("FRAT TRACER connected to internal");
}

FratTracer::~FratTracer () {
  LOG ("FRAT TRACER delete");
  delete file;
}

/*------------------------------------------------------------------------*/

inline void FratTracer::put_binary_zero () {
  assert (binary);
  assert (file);
  file->put ((unsigned char) 0);
}

inline void FratTracer::put_binary_lit (int lit) {
  assert (binary);
  assert (file);
  assert (lit != INT_MIN);
  unsigned x = 2 * abs (lit) + (lit < 0);
  unsigned char ch;
  while (x & ~0x7f) {
    ch = (x & 0x7f) | 0x80;
    file->put (ch);
    x >>= 7;
  }
  ch = x;
  file->put (ch);
}

inline void FratTracer::put_binary_id (uint64_t id) {
  assert (binary);
  assert (file);
  uint64_t x = id;
  unsigned char ch;
  while (x & ~0x7f) {
    ch = (x & 0x7f) | 0x80;
    file->put (ch);
    x >>= 7;
  }
  ch = x;
  file->put (ch);
}

/*------------------------------------------------------------------------*/

void FratTracer::frat_add_original_clause (uint64_t id,
                                           const vector<int> &clause) {
  if (binary)
    file->put ('o');
  else
    file->put ("o ");
  if (binary)
    put_binary_id (id);
  else
    file->put (id), file->put ("  ");
  for (const auto &external_lit : clause)
    if (binary)
      put_binary_lit (external_lit);
    else
      file->put (external_lit), file->put (' ');
  if (binary)
    put_binary_zero ();
  else
    file->put ("0\n");
}

void FratTracer::frat_add_derived_clause (uint64_t id,
                                          const vector<int> &clause) {
  if (binary)
    file->put ('a');
  else
    file->put ("a ");
  if (binary)
    put_binary_id (id);
  else
    file->put (id), file->put ("  ");
  for (const auto &external_lit : clause)
    if (binary)
      put_binary_lit (external_lit);
    else
      file->put (external_lit), file->put (' ');
  if (binary)
    put_binary_zero ();
  else
    file->put ("0\n");
}

void FratTracer::frat_add_derived_clause (uint64_t id,
                                          const vector<int> &clause,
                                          const vector<uint64_t> &chain) {
  if (binary)
    file->put ('a');
  else
    file->put ("a ");
  if (binary)
    put_binary_id (id);
  else
    file->put (id), file->put ("  ");
  for (const auto &external_lit : clause)
    if (binary)
      put_binary_lit (external_lit);
    else
      file->put (external_lit), file->put (' ');
  if (binary)
    put_binary_zero (), file->put ('l');
  else
    file->put ("0  l ");
  for (const auto &c : chain)
    if (binary)
      put_binary_id (2 * c); // lrat can have negative ids
    else
      file->put (c), file->put (' '); // in proof chain, so they get
  if (binary)
    put_binary_zero (); // since cadical has no rat-steps
  else
    file->put ("0\n"); // this is just 2c here
}

void FratTracer::frat_delete_clause (uint64_t id,
                                     const vector<int> &clause) {
  if (binary)
    file->put ('d');
  else
    file->put ("d ");
  if (binary)
    put_binary_id (id);
  else
    file->put (id), file->put ("  ");
  for (const auto &external_lit : clause)
    if (binary)
      put_binary_lit (external_lit);
    else
      file->put (external_lit), file->put (' ');
  if (binary)
    put_binary_zero ();
  else
    file->put ("0\n");
}

void FratTracer::frat_finalize_clause (uint64_t id,
                                       const vector<int> &clause) {
  if (binary)
    file->put ('f');
  else
    file->put ("f ");
  if (binary)
    put_binary_id (id);
  else
    file->put (id), file->put ("  ");
  for (const auto &external_lit : clause)
    if (binary)
      put_binary_lit (external_lit);
    else
      file->put (external_lit), file->put (' ');
  if (binary)
    put_binary_zero ();
  else
    file->put ("0\n");
}

/*------------------------------------------------------------------------*/

void FratTracer::add_original_clause (uint64_t id, bool,
                                      const vector<int> &clause, bool) {
  if (file->closed ())
    return;
  LOG ("FRAT TRACER tracing addition of original clause");
  frat_add_original_clause (id, clause);
}

void FratTracer::add_derived_clause (uint64_t id, bool,
                                     const vector<int> &clause,
                                     const vector<uint64_t> &chain) {
  if (file->closed ())
    return;
  LOG ("FRAT TRACER tracing addition of derived clause");
  if (with_antecedents)
    frat_add_derived_clause (id, clause, chain);
  else
    frat_add_derived_clause (id, clause);
  added++;
}

void FratTracer::delete_clause (uint64_t id, bool,
                                const vector<int> &clause) {
  if (file->closed ())
    return;
  LOG ("FRAT TRACER tracing deletion of clause");
  frat_delete_clause (id, clause);
  deleted++;
}

void FratTracer::finalize_clause (uint64_t id, const vector<int> &clause) {
  if (file->closed ())
    return;
  LOG ("FRAT TRACER tracing finalization of clause");
  frat_finalize_clause (id, clause);
}

/*------------------------------------------------------------------------*/

bool FratTracer::closed () { return file->closed (); }

void FratTracer::close () {
  assert (!closed ());
  file->close ();
}

void FratTracer::flush () {
  assert (!closed ());
  file->flush ();
  MSG ("traced %" PRId64 " original, %" PRId64 " added clauses, %" PRId64
       " deleted clauses and %" PRId64 " finalized clauses",
       original, added, deleted, finalized);
}

} // namespace CaDiCaL
