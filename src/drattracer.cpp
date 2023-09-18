#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

DratTracer::DratTracer (Internal *i, File *f, bool b)
    : internal (i), file (f), binary (b),
      added (0), deleted (0) {
  (void) internal;
  LOG ("DRAT TRACER new");
}

DratTracer::~DratTracer () {
  LOG ("DRAT TRACER delete");
  delete file;
}

/*------------------------------------------------------------------------*/


inline void DratTracer::put_binary_zero () {
  assert (binary);
  assert (file);
  file->put ((unsigned char) 0);
}

inline void DratTracer::put_binary_lit (int lit) {
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

inline void DratTracer::put_binary_id (uint64_t id) {
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

void DratTracer::drat_add_clause (const vector<int> &clause) {
  if (binary)
    file->put ('a');
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
void DratTracer::drat_delete_clause (const vector<int> &clause) {
  if (binary)
    file->put ('d');
  else
    file->put ("d ");
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


void DratTracer::add_derived_clause (uint64_t, bool, const vector<int> &clause,
                                 const vector<uint64_t> &) {
  if (file->closed ())
    return;
  LOG ("DRAT TRACER tracing addition of derived clause");
  drat_add_clause (clause);
  added++;
}

void DratTracer::delete_clause (uint64_t, bool, const vector<int> &clause) {
  if (file->closed ())
    return;
  LOG ("DRAT TRACER tracing deletion of clause");
  drat_delete_clause (clause);
  deleted++;
}


/*------------------------------------------------------------------------*/

bool DratTracer::closed () { return file->closed (); }

void DratTracer::close () {
  assert (!closed ());
  file->close ();
}

void DratTracer::flush () {
  assert (!closed ());
  file->flush ();
  MSG ("traced %" PRId64 " added and %" PRId64 " deleted clauses", added,
       deleted);
}

} // namespace CaDiCaL
