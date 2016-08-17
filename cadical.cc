#include <cstdarg>
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <vector>
#include <algorithm>
#include <climits>

using namespace std;

/*------------------------------------------------------------------------*/

static void msg (const char * fmt, ...) {
  va_list ap;
  fputs ("c ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

#ifdef LOGGING
#define LOG(FMT,ARGS...) do { msg (FMT, ##ARGS); } while (0)
#else
#define LOG(ARGS...) do { } while (0)
#endif

static void die (const char * fmt, ...) {
  va_list ap;
  fputs ("*** cadical error: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

#include <sys/time.h>
#include <sys/resource.h>

static double seconds (void) {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

/*------------------------------------------------------------------------*/

struct Var {
  long bumped;
  bool seen, minimized, poison;
  Var * prev, * next;
  Var () :
    bumped (0),
    seen (false), minimized (false), poison (false),
    prev (0), next (0)
  { }
};

struct Clause {
  int size, glue;
  long resolved;
  bool redundant, garbage;
  int literals[1];
};

struct Watch {
  int blit;
  Clause * clause;
  Watch (int b, Clause * c) : blit (b), clause (c) { }
};

typedef vector<Watch> Watches;

/*------------------------------------------------------------------------*/

static int max_var, num_original_clauses;

static Var * vars;
static signed char * vals;
static Watches * all_literal_watches;
static struct { Var * first, * last, * next; } queue;

static vector<int> literals, units, trail;
static vector<Clause*> irredundant, redundant;

static long conflicts, decisions, restarts, propagations, bumped;

static struct { 
  struct { double glue, size; } resolved;
  struct { struct { double fast, slow; } glue; } learned;
} ema;

/*------------------------------------------------------------------------*/

static int val (int lit) {
  assert (lit), assert (abs (lit) <= max_var);
  int res = vals[abs (lit)];
  if (lit < 0) res = -res;
  return res;
}

static int sign (int lit) {
  assert (lit), assert (abs (lit) <= max_var);
  return lit < 0 ? -1 : 1;
}

static Watches & watches (int lit) {
  assert (lit), assert (abs (lit) <= max_var);
  return all_literal_watches[2*abs (lit) + (lit < 0)];
}

/*------------------------------------------------------------------------*/

#ifdef LOGGING
static void msg (Clause * c, const char * fmt, ...) {
  va_list ap;
  fputs ("c ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  if (c->redundant) printf (" redundant glue %d", c->glue);
  else printf (" irredundant");
  printf (" size %d clause", c->size);
  for (const int * p = 0; *p; p++) printf (" %d", *p);
  fputc ('\n', stdout);
  fflush (stdout);
}
#endif

static Clause * new_clause (bool red, int glue) {
  assert (literals.size () <= (size_t) INT_MAX);
  int size = (int) literals.size ();
  Clause * res = (Clause*) new char[sizeof *res + sizeof (int)];
  res->size = size;
  res->glue = glue;
  res->resolved = conflicts;
  res->redundant = red;
  res->garbage = false;
  for (int i = 0; i < size; i++) res->literals[i] = literals[i];
  res->literals[size] = 0;
  if (red) redundant.push_back (res);
  else irredundant.push_back (res);
  LOG (res, "new");
  return res;
}

static Clause * new_original_clause () { return new_clause (false, 0); }
static Clause * new_learned_clause (int g) { return new_clause (true, g); }

static void delete_clause (Clause * c) { 
  LOG (c, "delete");
  delete [] (char*) c;
}

/*------------------------------------------------------------------------*/

static int solve () {
  return 0;
}

/*------------------------------------------------------------------------*/

static void init_queue () {
  Var * prev = 0;
  for (int i = 1; i <= max_var; i++) {
    Var * v = &vars[i];
    if ((v->prev = prev)) prev->next = v;
    else queue.first = v;
    prev = v;
  }
  queue.last = queue.next = prev;
}

static void init () {
  vals = new signed char[max_var + 1];
  vars = new Var[max_var + 1];
  all_literal_watches = new Watches[2*(max_var + 1)];
  for (int i = 1; i <= max_var; i++) vals[i] = 0;
  init_queue ();
  msg ("initialized %d variables", max_var);
}

static void reset () {
  for (size_t i = 0; i < irredundant.size (); i++)
    delete_clause (irredundant[i]);
  for (size_t i = 0; i < redundant.size (); i++)
    delete_clause (redundant[i]);
  delete [] all_literal_watches;
  delete [] vars;
  delete [] vals;
}

/*------------------------------------------------------------------------*/

static FILE * input, * proof;
static int close_input, close_proof;
static const char * input_name, * proof_name;

static bool has_suffix (const char * str, const char * suffix) {
  int k = strlen (str), l = strlen (suffix);
  return k > l && !strcmp (str + k - l, suffix);
}

static FILE * read_pipe (const char * fmt, const char * path) {
  char * cmd = (char*) malloc (strlen (fmt) + strlen (path));
  sprintf (cmd, fmt, path);
  FILE * res = popen (cmd, "r");
  free (cmd);
  return res;
}

static const char * USAGE =
"usage: cadical [ -h ] [ <input> [ <proof> ] ]\n"
"\n"
"where '<input>' is a (compressed) DIMACS file and '<output>'\n"
"is a file to store the DRAT proof.  If no '<proof>' file is\n"
"specified, then no proof is generated.  If no '<input>' is given\n"
"then '<stdin>' is used. If '-' is used as '<input>' then the\n"
"solver reads from '<stdin>'.  If '-' is specified for '<proof>'\n"
"then the proof is generated and printed to '<stdout>'.\n";

struct lit_less_than {
  bool operator () (const int a, const int b) const {
    int res = abs (a) - abs (b);
    if (res) return res;
    return a < b ? -1 : 1;
  }
};

static bool tautological () {
  sort (literals.begin (), literals.end (), lit_less_than ());
  return true;
}

static void parse_dimacs () {
  int ch;
  for (;;) {
    ch = getc (input);
    if (ch != 'c') break;
    while ((ch = getc (input)) != '\n')
      if (ch == EOF)
	die ("unexpected end-of-file in header comment");
  }
  if (ch != 'p') die ("expected 'c' or 'p'");
  if (fscanf (input, " cnf %d %d", &max_var, &num_original_clauses) != 2 ||
      max_var < 0 || num_original_clauses < 0)
    die ("invalid 'p ...' header");
  msg ("found 'p cnf %d %d' header", max_var, num_original_clauses);
  init ();
  int lit = 0, parsed_clauses = 0;
  while (fscanf (input, "%d", &lit) == 1) {
    if (lit == INT_MIN || abs (lit) > max_var)
      die ("invalid literal %d", lit);
    if (lit) literals.push_back (lit);
    else if (!tautological ()) new_original_clause ();
    literals.clear ();
    parsed_clauses++;
  }
  if (lit) die ("last clause without '0'");
  if (parsed_clauses + 1 < num_original_clauses) die ("clauses missing");
  if (parsed_clauses < num_original_clauses) die ("clause missing");
  if (parsed_clauses > num_original_clauses) die ("too many clauses");
  msg ("parsed %d clauses in %.2f seconds", parsed_clauses, seconds ());
}

static double relative (double a, double b) { return b ? a / b : 0; }

static void print_statistics () {
  double t = seconds ();
  msg ("");
  msg ("conflicts:    %22ld   %10.2f per second",
    conflicts, relative (conflicts, t));
  msg ("decisions:    %22ld   %10.2f per second",
    decisions, relative (decisions, t));
  msg ("restarts:     %22ld   %10.2f per second",
    restarts, relative (restarts, t));
  msg ("propagations: %22ld   %10.2f per second",
    propagations, relative (propagations, t));
  msg ("time:         %22s   %10.2f seconds", "", t);
  msg ("");
}

int main (int argc, char ** argv) {
  int i, res;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) fputs (USAGE, stdout), exit (0);
    else if (!strcmp (argv[i], "-")) {
      if (proof) die ("too many arguments");
      else if (!input) input = stdin, input_name = "<stdin>";
      else proof = stdout, proof_name = "<stdout>";
    } else if (argv[i][0] == '-')
    die ("invalid option '%s'", argv[i]);
    else if (proof) die ("too many arguments");
    else if (input) {
      if (!(proof = fopen (argv[i], "w")))
	die ("can not open and write DRAT proof to '%s'", argv[i]);
      proof_name = argv[i], close_proof = 1;
    } else {
      if (has_suffix (argv[i], ".bz2"))
	input = read_pipe ("bzcat %s", argv[i]), close_input = 2;
      else if (has_suffix (argv[i], ".gz"))
	input = read_pipe ("gunzip -c %s", argv[i]), close_input = 2;
      else input = fopen (argv[i], "r"), close_input = 1;
      if (!input)
	die ("can not open and read DIMACS file '%s'", argv[i]);
      input_name = argv[i];
    }
  }
  if (!input) input_name = "<stdin>", input = stdin;
  msg ("CaDiCaL Radically Simplified CDCL Solver Version " VERSION);
  msg ("");
  msg ("reading DIMACS file from '%s'", input_name);
  if (proof) msg ("writing DRAT proof to '%s'", proof_name);
  else msg ("will not generate nor write DRAT proof");
  if (close_input == 1) fclose (input);
  if (close_input == 2) pclose (input);
  parse_dimacs ();
  res = solve ();
  if (close_proof) fclose (proof);
  reset ();
  print_statistics ();
  msg ("exit %d", res);
  return res;
}
