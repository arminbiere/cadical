#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

Tracer::Tracer (Internal *i, File *f, bool b, bool lrat, bool frat,
                bool veripb)
    : internal (i), file (f), binary (b), lrat (lrat), _flushed (false),
      frat (frat), veripb (veripb), added (0), deleted (0), latest_id (0) {
  (void) internal;
  LOG ("TRACER new");
}

Tracer::~Tracer () {
  LOG ("TRACER delete");
  delete file;
}

/*------------------------------------------------------------------------*/

// Support for binary DRAT format.

inline void Tracer::put_binary_zero () {
  assert (binary);
  assert (file);
  file->put ((unsigned char) 0);
}

inline void Tracer::put_binary_lit (int lit) {
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

// Support for binary FRAT (TODO: maybe merge with function above
// because this is copy pasta)

inline void Tracer::put_binary_id (uint64_t id) {
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

void Tracer::lrat_add_clause (uint64_t id, const vector<int> &clause,
                              const vector<uint64_t> &chain) {
  LOG ("TRACER LRAT tracing addition of derived clause with proof chain");

  if (delete_ids.size ()) {
    // if (binary) put_binary_id (latest_id);
    // if (binary) file->put ('d');
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

void Tracer::lrat_delete_clause (uint64_t id) {
  LOG ("TRACER LRAT tracing deletion of clause");
  delete_ids.push_back (id); // pushing off deletion for later
}

/*------------------------------------------------------------------------*/

void Tracer::frat_add_original_clause (uint64_t id,
                                       const vector<int> &clause) {
  LOG ("TRACER FRAT tracing addition of original clause");
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
void Tracer::frat_add_derived_clause (uint64_t id,
                                      const vector<int> &clause) {
  LOG (
      "TRACER FRAT tracing addition of derived clause without proof chain");
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
void Tracer::frat_add_derived_clause (uint64_t id,
                                      const vector<int> &clause,
                                      const vector<uint64_t> &chain) {
  LOG ("TRACER FRAT tracing addition of derived clause with proof chain");
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
void Tracer::frat_delete_clause (uint64_t id, const vector<int> &clause) {
  LOG ("TRACER FRAT tracing deletion of clause");
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
void Tracer::frat_finalize_clause (uint64_t id, const vector<int> &clause) {
  LOG ("TRACER FRAT tracing finalization of clause");
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

void Tracer::drat_add_clause (const vector<int> &clause) {
  LOG ("TRACER DRAT tracing addition of derived clause");
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
void Tracer::drat_delete_clause (const vector<int> &clause) {
  LOG ("TRACER DRAT tracing deletion of clause");
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

void Tracer::veripb_finalize_proof (uint64_t conflict_id) {
  if (file->closed () || !veripb)
    return;
  LOG ("TRACER veriPB tracing finalization of proof");
  file->put ("output NONE\n");
  file->put ("conclusion UNSAT : ");
  file->put (conflict_id);
  file->put (" \n");
  file->put ("end pseudo-Boolean proof\n");
}

void Tracer::veripb_add_derived_clause (const vector<int> &clause,
                                        const vector<uint64_t> &chain) {
  LOG ("TRACER veriPB tracing addition of derived clause");
  file->put ("pol ");
  bool first = true;
  for (auto p = chain.rbegin (); p != chain.rend (); p++) {
    auto cid = *p;
    if (first) {
      first = false;
      file->put (cid);
    } else {
      file->put (' ');
      file->put (cid);
      file->put (" + s");
    }
  }
  file->put ("\n");
  file->put ("e -1 ");
  for (const auto &external_lit : clause) {
    file->put ("1 ");
    if (external_lit < 0)
      file->put ('~');
    file->put ('x');
    file->put (abs (external_lit));
    file->put (' ');
  }
  file->put (">= 1 ;\n");
}

void Tracer::veripb_begin_proof (uint64_t reserved_ids) {
  LOG ("TRACER veriPB tracing start of proof");
  file->put ("pseudo-Boolean proof version 2.0\n");
  file->put ("f ");
  file->put (reserved_ids);
  file->put ("\n");
}

void Tracer::veripb_delete_clause (uint64_t id) {
  LOG ("TRACER veriPB tracing deletion of clause");
  file->put ("del id ");
  file->put (id);
  file->put ("\n");
}

/*------------------------------------------------------------------------*/

void Tracer::add_original_clause (uint64_t id, const vector<int> &clause) {
  if (file->closed ())
    return;
  else if (frat)
    frat_add_original_clause (id, clause);
}

void Tracer::add_derived_clause (uint64_t id, const vector<int> &clause) {
  if (file->closed ())
    return;
  if (frat)
    frat_add_derived_clause (id, clause);
  else {
    assert (!lrat && !veripb);
    drat_add_clause (clause);
  }
  added++;
  _flushed = false;
}

void Tracer::add_derived_clause (uint64_t id, const vector<int> &clause,
                                 const vector<uint64_t> &chain) {
  if (file->closed ())
    return;
  if (veripb)
    veripb_add_derived_clause (clause, chain);
  else if (frat)
    frat_add_derived_clause (id, clause, chain);
  else if (lrat)
    lrat_add_clause (id, clause, chain);
  else
    drat_add_clause (clause);
  added++;
  _flushed = false;
}

void Tracer::delete_clause (uint64_t id, const vector<int> &clause) {
  if (file->closed ())
    return;
  if (veripb)
    veripb_delete_clause (id);
  else if (frat)
    frat_delete_clause (id, clause);
  else if (lrat)
    lrat_delete_clause (id);
  else
    drat_delete_clause (clause);
  deleted++;
  _flushed = false;
}

void Tracer::finalize_clause (uint64_t id, const vector<int> &clause) {
  if (file->closed ())
    return;
  if (frat)
    frat_finalize_clause (id, clause);
}

void Tracer::set_first_id (uint64_t id) {
  latest_id = id;
  if (file->closed ())
    return;
  if (veripb)
    veripb_begin_proof (id);
}

/*------------------------------------------------------------------------*/

bool Tracer::closed () { return file->closed (); }

void Tracer::close (bool print) {
  assert (!closed ());
  if (!flushed ())
    flush (print);
  file->close (print);
}

void Tracer::flush (bool print) {
  if (flushed ())
    return;
  assert (!closed ());
  file->flush ();
#ifndef QUIET
  if (!internal->opts.quiet)
    if (print || internal->opts.verbose > 0)
      MSG ("traced %" PRId64 " added and %" PRId64 " deleted clauses",
           added, deleted);
#else
  (void) print;
#endif
  _flushed = true;
}

} // namespace CaDiCaL
