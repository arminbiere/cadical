#include "../../src/ipasir2.h"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <assert.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

#if __GNUC__ > 4 || defined(__llvm__)
static const int n = 8;
#else
static const int n = 10;
#endif

static int ph (int p, int h) {
  assert (0 <= p), assert (p < n + 1);
  assert (0 <= h), assert (h < n);
  return 1 + h * (n + 1) + p;
}

// Construct a pigeon hole formula for 'n+1' pigeons in 'n' holes.
//
static int formula (void *solver) {
  int max = 0;
  int *clause = (int *) malloc ((n) * sizeof (int));
  for (int h = 0; h < n; h++) {
    for (int p1 = 0; p1 < n + 1; p1++) {
      for (int p2 = p1 + 1; p2 < n + 1; p2++) {
        clause[0] = -ph (p1, h);
        clause[1] = -ph (p2, h);
        ipasir2_add (solver, clause, 2, 0, 0);
        if (max < ph (p1, h))
          max = ph (p1, h);
        if (max < ph (p2, h))
          max = ph (p2, h);
      }
    }
  }

  int i = 0;
  for (int p = 0; p < n + 1; p++) {
    for (int h = 0; h < n; h++) {
      clause[i++] = ph (p, h);
    }
    ipasir2_add (solver, clause, i, 0, 0);
    printf ("adding clause of length %d\n", i);
    i = 0;
  }
  free (clause);
  return max;
}

typedef struct learner learner;

struct learner {
  void *solver;
  int max_var;
  unsigned learned;
  unsigned aborted;
};

static void learn (void *ptr, int32_t const *clause, int32_t len,
                   void *proofmeta) {
  learner *learner = ptr;
  int max = learner->max_var;
  for (const int *p = clause; p != clause + len; p++) {
    if (*p > max || -*p > max) {
      learner->aborted++;
      fprintf (stderr, "out of bound literal %d", *p);
      return;
    }
  }
  ipasir2_add (learner->solver, clause, len, 0, proofmeta);
  learner->learned++;
}

static int terminator (void *ptr) { return *(int *) ptr; }

static int terminate;

static void (*saved) (int);

static void handler (int sig) {
  assert (sig == SIGALRM);
  signal (SIGALRM, saved);
  *(volatile int *) &terminate = 1;
}

static void *solvers[2];
static learner learners[2];

int main (void) {
  ipasir2_errorcode ret = IPASIR2_E_UNKNOWN;
  const char *signature;
  ret = ipasir2_signature (&signature);
  assert (ret == IPASIR2_E_OK);

  printf ("signature '%s'\n", signature);
  for (int i = 0; i < 2; i++) {
    ipasir2_init (&solvers[i]);
    learners[i].solver = solvers[i];
    ret = ipasir2_set_export (solvers[i], learners + !i, 4, learn);
    assert (ret == IPASIR2_E_OK);
    learners[i].max_var = formula (solvers[i]);
  }
  unsigned round = 0;
  int active = 0;
  int res = 0;
  for (;;) {
    printf ("round %d active %d imported %u aborted %u\n", ++round, active,
            learners[active].learned, learners[active].aborted);
    fflush (stdout);
    saved = signal (SIGALRM, handler);
#if __GNUC__ > 4 || defined(__llvm__)
    struct timeval value;
    value.tv_sec = 0;
    value.tv_usec = 2e4;

    struct timeval interval;
    interval.tv_sec = 0;
    interval.tv_usec = 0;

    struct itimerval t;
    t.it_interval = interval;
    t.it_value = value;
    setitimer (0, &t, NULL);
#else
    alarm (1);
#endif
    ret = ipasir2_set_terminate (solvers[active], &terminate, terminator);
    assert (ret == IPASIR2_E_OK);
    ret = ipasir2_solve (solvers[active], &res, 0, 0);
    assert (ret == IPASIR2_E_OK);
    if (res)
      break;
    *(volatile int *) &terminate = 0;
    active = !active;
  }
  for (int i = 0; i < 2; i++)
    ipasir2_release (solvers[i]);
  for (int i = 0; i < 2; i++) {
    printf ("solver[%d] imported %u, aborted %u clauses\n", i,
            learners[i].learned, learners[i].aborted);
  }
  return 0;
}
