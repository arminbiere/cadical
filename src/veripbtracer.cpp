#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

VeripbTracer::VeripbTracer (Internal *i, File *f, bool b, bool a)
    : internal (i), file (f), binary (b), with_antecedents (a),
      added (0), deleted (0) {
  (void) internal;
  LOG ("VERIPB TRACER new");
}

VeripbTracer::~VeripbTracer () {
  LOG ("VERIPB TRACER delete");
  delete file;
}

/*------------------------------------------------------------------------*/


inline void VeripbTracer::put_binary_zero () {
  assert (binary);
  assert (file);
  file->put ((unsigned char) 0);
}

inline void VeripbTracer::put_binary_lit (int lit) {
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

inline void VeripbTracer::put_binary_id (uint64_t id) {
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


void VeripbTracer::veripb_add_derived_clause (bool redundant, const vector<int> &clause,
                                        const vector<uint64_t> &chain) {
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

void VeripbTracer::veripb_add_derived_clause (bool redundant, const vector<int> &clause) {
  file->put ("pol ");
  bool first = true;
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

void VeripbTracer::veripb_begin_proof (uint64_t reserved_ids) {
  file->put ("pseudo-Boolean proof version 2.0\n");
  file->put ("f ");
  file->put (reserved_ids);
  file->put ("\n");
}

void VeripbTracer::veripb_delete_clause (bool redundant, uint64_t id) {
  file->put ("del id ");
  file->put (id);
  file->put ("\n");
}

void VeripbTracer::veripb_finalize_proof (uint64_t conflict_id) {
  file->put ("output NONE\n");
  file->put ("conclusion UNSAT : ");
  file->put (conflict_id);
  file->put (" \n");
  file->put ("end pseudo-Boolean proof\n");
}



/*------------------------------------------------------------------------*/

void VeripbTracer::begin_proof (uint64_t id) {
  if (file->closed ())
    return;
  LOG ("VERIPB TRACER tracing start of proof");
  veripb_begin_proof (id);
}


void VeripbTracer::add_derived_clause (uint64_t, bool redundant, const vector<int> &clause,
                                 const vector<uint64_t> &chain) {
  if (file->closed ())
    return;
  LOG ("VERIPB TRACER tracing addition of derived clause");
  if (with_antecedents)
    veripb_add_derived_clause (redundant, clause, chain);
  else
    veripb_add_derived_clause (redundant, clause);
  added++;
}

void VeripbTracer::delete_clause (uint64_t id, bool redundant, const vector<int> &) {
  if (file->closed ())
    return;
  LOG ("VERIPB TRACER tracing deletion of clause");
  veripb_delete_clause (id, redundant);
  deleted++;
}


void VeripbTracer::finalize_proof (uint64_t conflict_id) {
  if (file->closed ())
    return;
  LOG ("VERIPB TRACER tracing finalization of proof");
  veripb_finalize_proof (conflict_id);
}

/*------------------------------------------------------------------------*/

bool VeripbTracer::closed () { return file->closed (); }

void VeripbTracer::close () {
  assert (!closed ());
  file->close ();
}

void VeripbTracer::flush () {
  assert (!closed ());
  file->flush ();
  MSG ("traced %" PRId64 " added and %" PRId64 " deleted clauses", added,
       deleted);
}

} // namespace CaDiCaL
