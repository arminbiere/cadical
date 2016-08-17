#include <cstdarg>
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <vector>

using namespace std;

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
#define LOG(FMT,ARGS...) do { msg (" LOG " FMT, ##ARGS); } while (0)
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

static FILE * proof, * input;
static int close_input;
static const char * input_name, * proof_name;

static int has_suffix (const char * str, const char * suffix) {
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
"where '<input>' is a (compressed) DIMACS file and '<output>'\n"
"is a file to store the DRAT proof.  If no '<proof>' file is\n"
"specified, then no proof is generated.  If no '<input>' is given\n"
"then '<stdin>' is used. If '-' is used as '<input>' then the\n"
"solver reads from '<stdin>'.  If '-' is specified for '<proof>'\n"
"then the proof is generated and printed to '<stdout>'.\n";

static void usage () {
  fputs (USAGE, stdout);
  exit (0);
} 

int main (int argc, char ** argv) {
  int i, res = 0;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) usage ();
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
      proof_name = argv[i];
    } else {
      close_input = 2;
      input_name = argv[i];
      if (has_suffix (argv[i], ".bz2"))
	input = read_pipe ("bzcat %s", argv[i]);
      else input = fopen (argv[i], "r"), close_input = 1;
      if (!input)
	die ("can not open and read DIMACS file '%s'", argv[i]);
    }
  }
  if (!input) input_name = "<stdin>", input = stdin;
  msg ("CaDiCaL Radically Simplified CDCL Solver " VERSION);
  msg ("reading DIMACS file from '%s'", input_name);
  if (proof) msg ("writing DRAT proof to '%s'", proof_name);
  else msg ("will not generate nor write DRAT proof");
  if (close_input == 1) fclose (input);
  if (close_input == 2) pclose (input);
  if (proof) fclose (proof);
  return res;
}
