// Check old freeze/melt semantics.  Example from 'lglib.h' (Lingeling).

#include "../../src/ccadical.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <fcntl.h>
#include <signal.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

void illegal (void (*f) (CCaDiCaL *, int), CCaDiCaL *cadical, int lit) {
  pid_t child = fork (), other;
  int status;
  if (!child) {
    int null = open ("/dev/null", O_WRONLY);
    dup2 (null, 2);
    f (cadical, lit);
    close (2);
    exit (0);
  }
  other = wait (&status);
  assert (other == child);
  assert (!WIFEXITED (status));
  assert (WIFSIGNALED (status));
  assert (WTERMSIG (status) == SIGABRT);
}

int main (void) {

  CCaDiCaL *cadical = ccadical_init ();
  int res;

  ccadical_set_option (cadical, "check", 1);
  ccadical_set_option (cadical, "checkfrozen", 1);

  ccadical_add (cadical, -14);
  ccadical_add (cadical, 2);
  ccadical_add (cadical, 0); // binary clause

  ccadical_add (cadical, 14);
  ccadical_add (cadical, -1);
  ccadical_add (cadical, 0); // binary clause

  ccadical_assume (cadical, 1);  // assume '1'
  ccadical_freeze (cadical, 1);  // will use '1' below
  ccadical_freeze (cadical, 14); // will use '14 too
  assert (ccadical_frozen (cadical, 1));
  assert (ccadical_frozen (cadical, 14));
  res = ccadical_solve (cadical);
  assert (res == 10);
  (void) ccadical_val (cadical, 1);  // fine
  (void) ccadical_val (cadical, 2);  // fine
  (void) ccadical_val (cadical, 3);  // fine !
  (void) ccadical_val (cadical, 14); // fine

  illegal (ccadical_add, cadical, 2);    // ILLEGAL
  illegal (ccadical_assume, cadical, 2); // ILLEGAL

  ccadical_add (cadical, -14);
  ccadical_add (cadical, 1);
  ccadical_add (cadical, 0); // binary clause

  ccadical_add (cadical, 15);
  ccadical_add (cadical, 0);   // fine!
  ccadical_melt (cadical, 14); // '1' discarded

  res = ccadical_solve (cadical);
  assert (res == 10);
  assert (ccadical_frozen (cadical, 1));
  (void) ccadical_val (cadical, 1);  // fine
  (void) ccadical_val (cadical, 2);  // fine
  (void) ccadical_val (cadical, 3);  // fine
  (void) ccadical_val (cadical, 14); // fine
  (void) ccadical_val (cadical, 15); // fine

  illegal (ccadical_assume, cadical, 2);  // ILLEGAL
  illegal (ccadical_assume, cadical, 14); // ILLEGAL

  ccadical_add (cadical, 1); // still frozen
  ccadical_melt (cadical, 1);
  ccadical_add (cadical, 0);
  res = ccadical_solve (cadical);
  assert (res == 10); // TODO right?
  ccadical_reset (cadical);

  return 0;
}
