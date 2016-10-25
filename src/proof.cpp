#include "proof.hpp"
#include "internal.hpp"
#include "logging.hpp"
#include "clause.hpp"
#include "file.hpp"

#include <cassert>
#include <climits>

namespace CaDiCaL {

using namespace std;

void Internal::close_proof () {
  if (!proof) return;
  LOG ("closing proof");
  delete proof;
  proof = 0;
}

Proof::Proof (Internal * s, File * f, bool b, bool o) :
internal (s), file (f), binary (b), owned (o)
{ }

Proof::~Proof () { if (owned) delete file; }

void Internal::new_proof (File * file, bool o) {
  close_proof ();
  proof = new Proof (this, file, opts.binary, o);
}

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

void Proof::trace_empty_clause () {
  LOG ("tracing empty clause");
  if (binary) file->put ('a'), put_binary_zero ();
  else file->put ("0\n");
}

void Proof::trace_unit_clause (int unit) {
  LOG ("tracing unit clause %d", unit);
  if (binary) file->put ('a'), put_binary_lit (unit), put_binary_zero ();
  else file->put (unit), file->put (" 0\n");
}

inline void Proof::trace_clause (Clause * c, bool add) {
  if (binary) file->put (add ? 'a' : 'd');
  else if (!add) file->put ("d ");
  const const_literal_iterator end = c->end ();
  const_literal_iterator i = c->begin ();
  while (i != end)
    if (binary) put_binary_lit (*i++);
    else file->put (*i++), file->put (" ");
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

void Proof::trace_flushing_clause (Clause * c) {
  LOG (c, "tracing flushing fixed");
  if (binary) file->put ('a');
  const const_literal_iterator end = c->end ();
  for (const_literal_iterator i = c->begin (); i != end; i++) {
    const int lit = *i;
    if (internal->fixed (lit) < 0) continue;
    if (binary) put_binary_lit (lit);
    else file->put (lit), file->put (" ");
  }
  if (binary) put_binary_zero ();
  else file->put ("0\n");
  trace_clause (c, false);
}

void Proof::trace_strengthen_clause (Clause * c, int remove) {
  LOG (c, "tracing strengthen %d in", remove);
  if (binary) file->put ('a');
  const const_literal_iterator end = c->end ();
  for (const_literal_iterator i = c->begin (); i != end; i++) {
    const int lit = *i;
    if (lit == remove) continue;
    if (binary) put_binary_lit (lit);
    else file->put (lit), file->put (" ");
  }
  if (binary) put_binary_zero ();
  else file->put ("0\n");
  trace_clause (c, false);
}

};
