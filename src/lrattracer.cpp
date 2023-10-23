#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

LratTracer::LratTracer (Internal *i, File *f, bool b)
    : internal (i), file (f), binary (b), added (0), deleted (0),
      latest_id (0) {
  (void) internal;
}

void LratTracer::connect_internal (Internal *i) {
  internal = i;
  file->connect_internal (internal);
  LOG ("LRAT TRACER connected to internal");
}

LratTracer::~LratTracer () {
  LOG ("LRAT TRACER delete");
  delete file;
}

/*------------------------------------------------------------------------*/

inline void LratTracer::put_binary_zero () {
  assert (binary);
  assert (file);
  file->put ((unsigned char) 0);
}

inline void LratTracer::put_binary_lit (int lit) {
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

inline void LratTracer::put_binary_id (uint64_t id) {
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

void LratTracer::lrat_add_clause (uint64_t id, const vector<int> &clause,
                                  const vector<uint64_t> &chain) {
  if (delete_ids.size ()) {
    if (!binary)
      file->put (latest_id), file->put (" ");
    if (binary)
      file->put ('d');
    else
      file->put ("d ");
    for (auto &did : delete_ids) {
      if (binary)
        put_binary_id (2 * did); // to have the output format as drat-trim
      else
        file->put (did), file->put (" ");
    }
    if (binary)
      put_binary_zero ();
    else
      file->put ("0\n");
    delete_ids.clear ();
  }
  latest_id = id;

  if (binary)
    file->put ('a'), put_binary_id (id);
  else
    file->put (id), file->put (" ");
  for (const auto &external_lit : clause)
    if (binary)
      put_binary_lit (external_lit);
    else
      file->put (external_lit), file->put (' ');
  if (binary)
    put_binary_zero ();
  else
    file->put ("0 ");
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

void LratTracer::lrat_delete_clause (uint64_t id) {
  delete_ids.push_back (id); // pushing off deletion for later
}

/*------------------------------------------------------------------------*/

void LratTracer::add_derived_clause (uint64_t id, bool,
                                     const vector<int> &clause,
                                     const vector<uint64_t> &chain) {
  if (file->closed ())
    return;
  LOG ("LRAT TRACER tracing addition of derived clause");
  lrat_add_clause (id, clause, chain);
  added++;
}

void LratTracer::delete_clause (uint64_t id, bool, const vector<int> &) {
  if (file->closed ())
    return;
  LOG ("LRAT TRACER tracing deletion of clause");
  lrat_delete_clause (id);
  deleted++;
}

void LratTracer::begin_proof (uint64_t id) {
  if (file->closed ())
    return;
  LOG ("LRAT TRACER tracing begin of proof");
  latest_id = id;
}

/*------------------------------------------------------------------------*/

bool LratTracer::closed () { return file->closed (); }

void LratTracer::close () {
  assert (!closed ());
  file->close ();
}

void LratTracer::flush () {
  assert (!closed ());
  file->flush ();
  MSG ("traced %" PRId64 " added and %" PRId64 " deleted clauses", added,
       deleted);
}

} // namespace CaDiCaL
