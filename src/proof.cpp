#include "internal.hpp"

namespace CaDiCaL {

using namespace std;

/*------------------------------------------------------------------------*/

// Enable proof logging by allocating a 'Proof' object.

void Internal::new_proof (File * file, bool owned) {
  close_proof ();
  proof = new Proof (this, file, opts.binary, owned);
}

// We want to close a proof trace as soon we are done.

void Internal::close_proof () {
  if (!proof) return;
  LOG ("closing proof");
  delete proof;
  proof = 0;
}

/*------------------------------------------------------------------------*/

Proof::Proof (Internal * s, File * f, bool b, bool o)
:
  internal (s), file (f), binary (b), owned (o)
{
}

Proof::~Proof () { if (owned) delete file; }

/*------------------------------------------------------------------------*/

// Support for binary DRAT format.

inline void Proof::put_binary_zero () {
  assert (binary);
  assert (file);
  file->put ((unsigned char) 0);
}

inline void Proof::put_binary_lit (int lit) {
  assert (binary);
  assert (file);
  assert (lit != INT_MIN);
  unsigned x = 2*abs (lit) + (lit < 0);
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

void Proof::trace_empty_clause () {
  LOG ("tracing empty clause");
  if (binary) file->put ('a'), put_binary_zero ();
  else file->put ("0\n");
}

void Proof::trace_unit_clause (int unit) {
  LOG ("tracing unit clause %d", unit);
  const int elit = externalize (unit);
  if (binary) file->put ('a'), put_binary_lit (elit), put_binary_zero ();
  else file->put (elit), file->put (" 0\n");
}

/*------------------------------------------------------------------------*/

inline void Proof::trace_clause (Clause * c, bool add) {
  if (binary) file->put (add ? 'a' : 'd');
  else if (!add) file->put ("d ");
  const const_literal_iterator end = c->end ();
  const_literal_iterator i = c->begin ();
  while (i != end) {
    const int elit = externalize (*i++);
    if (binary) put_binary_lit (elit);
    else file->put (elit), file->put (" ");
  }
  if (binary) put_binary_zero ();
  else file->put ("0\n");
}

void Proof::trace_add_clause (Clause * c) {
  LOG (c, "tracing addition");
  trace_clause (c, true);
}

void Proof::trace_delete_clause (Clause * c) {
  LOG (c, "tracing deletion");
  trace_clause (c, false);
}

void Proof::trace_add_clause () {
  LOG (internal->clause, "tracing addition");
  if (binary) file->put ('a');
  const const_int_iterator end = internal->clause.end ();
  const_int_iterator i = internal->clause.begin ();
  while (i != end) {
    const int elit = externalize (*i++);
    if (binary) put_binary_lit (elit);
    else file->put (elit), file->put (" ");
  }
  if (binary) put_binary_zero ();
  else file->put ("0\n");
}

/*------------------------------------------------------------------------*/

// During garbage collection clauses are shrunken by removing falsified
// literals. To avoid copying the clause, we provide a specialized tracing
// function here, which traces the required 'add' and 'remove' operations.

void Proof::trace_flushing_clause (Clause * c) {
  LOG (c, "tracing flushing fixed");
  if (binary) file->put ('a');
  const const_literal_iterator end = c->end ();
  for (const_literal_iterator i = c->begin (); i != end; i++) {
    const int ilit = *i;
    if (internal->fixed (ilit) < 0) continue;
    const int elit = externalize (ilit);
    if (binary) put_binary_lit (elit);
    else file->put (elit), file->put (" ");
  }
  if (binary) put_binary_zero ();
  else file->put ("0\n");
  trace_clause (c, false);
}

// While strengthening clauses, e.g., through self-subsuming resolutions,
// during subsumption checking, we have a similar situation, except that we
// have to remove exactly one literal.  Again the following function allows
// to avoid copying the clause and instead provides tracing of the required
// 'add' and 'remove' operations.

void Proof::trace_strengthen_clause (Clause * c, int remove) {
  LOG (c, "tracing strengthen %d in", remove);
  if (binary) file->put ('a');
  const const_literal_iterator end = c->end ();
  for (const_literal_iterator i = c->begin (); i != end; i++) {
    const int ilit = *i;
    if (ilit == remove) continue;
    const int elit = externalize (ilit);
    if (binary) put_binary_lit (elit);
    else file->put (elit), file->put (" ");
  }
  if (binary) put_binary_zero ();
  else file->put ("0\n");
  trace_clause (c, false);
}

};
