/*------------------------------------------------------------------------*/

// Do include 'internal.hpp' but try to minimize internal dependencies.

#include "internal.hpp"
#include "signal.hpp"

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

class Solver;
class File;

// A wrapper app which makes up the CaDiCaL stand alone solver.  It in
// essence only consists of the 'App::main' function.  So this class
// contains code, which is not required if only the library interface in
// 'Solver' is used.  It further uses static data structures in order to
// have a signal handler catch signals.
//
// It is thus neither thread-safe nor reentrant.  If you want to use
// multiple instances of the solver use the 'Solver' interface directly
// which is thread-safe and reentrant among different solver instances.

class App : public Handler, public Terminator {

  // Global solver.

  Solver * solver;
  int time_limit;
  int max_var;
  int strict;   // 0=force, 1=relaxed, 2=strict
  bool timesup;

  // Printing.

  void print_usage (bool all = false);
  void print_witness (FILE *);

  // Option handling.

  bool verbose () { return get ("verbose") && !get ("quiet"); }

  int  get (const char*);
  bool set (const char*);
  bool set (const char*, int);

public:

  App ();
  ~App ();

  bool terminate () { return timesup; }

#ifndef QUIET
  void signal_message (const char * msg, int sig);
#endif
  void catch_signal (int sig);
  void catch_alarm ();

  int main (int arg, char ** argv);
};

/*------------------------------------------------------------------------*/

void App::print_usage (bool all) {
  printf (
"usage: cadical [ <option> ... ] [ <dimacs> [ <proof> ] ]\n"
"\n"
"where '<option>' is one of the following common options\n"
"\n"
"  -h             list of common options \n"
"  --help         list of advanced options\n"
"  --version      print version\n"
"\n"
"  -n             do not print witness%s\n"
#ifndef QUIET
"  -v             increase verbosity%s\n"
"  -q             be quiet%s\n"
#endif
"\n"
"  -t <sec>       set wall clock time limit\n"
,
  all ? " (same as '--no-witness')": ""
#ifndef QUIET
  , all ? " (see also '--verbose')": ""
  , all ? " (same as '--quiet')" : ""
#endif
  );

  if (all) {    // Print complete list of options.

    printf (
"\n"
"or one of the less common options\n"
"\n"
"  -O<level>      increase limits by '{2,10}^<level>' (default '0')\n"
"  -P<rounds>     enable preprocessing initially (default '0' rounds)\n"
"  -L<rounds>     run local search initialially (default '0' rounds)\n"
"\n"
"  -c <limit>     limit the number of conflicts (default unlimited)\n"
"  -d <limit>     limit the number of decisions (default unlimited)\n"
"\n"
"  -o <dimacs>    write simplified CNF in DIMACS format to file\n"
"  -e <extend>    write reconstruction/extension stack to file\n"
#ifdef LOGGING
"  -l             enable logging messages (same as '--log')\n"
#endif
"\n"
"  -f | --force   parse completely broken DIMACS header\n"
"  --strict       enforce strict parsing\n"
"\n"
"  -s <sol>       read solution in competition output format\n"
"                 to check consistency of learned clauses\n"
"                 during testing and debugging\n"
"\n"
"  --colors       force colored output\n"
"  --no-colors    disable colored output to terminal\n"
"  --no-witness   do not print witness (see also '-n' above)\n"
"\n"
"  --build        print build configuration\n"
"  --copyright    print copyright information\n"
"\n"
"or '<option>' is one of the following advanced internal options\n"
"\n");

    solver->usage ();

    fputs (
"\n"
"The internal options have their default value printed in brackets\n"
"after their description.  They can also be used in the form\n"
"'--<name>' which is equivalent to '--<name>=1' and in the form\n"
"'--no-<name>' which is equivalent to '--<name>=0'.  One can also\n"
"use 'true' instead of '1', 'false' instead of '0', as well as\n"
"numbers with positive exponent such as '1e3' instead of '1000'.\n"
"\n"
"Alternatively option values can also be specified in the header\n"
"of the DIMACS file, e.g., 'c --elim=false', or through environment\n"
"variables, such as 'CADICAL_ELIM=false'.  The embedded options in\n"
"the DIMACS file have highest priority, followed by command line\n"
"options and then values specified through environment variables.\n",
     stdout);

    printf (
"\n"
"There are also the following pre-defined configurations of options\n"
"\n");

    solver->configurations ();
  }

  // Common to both complete and common option usage.
  //
  fputs (
"\n"
"The input is read from '<dimacs>' assumed to be in DIMACS format.\n"
"If '<proof>' is given then a DRAT proof is written to that file.\n",
   stdout);

  if (all) {
    fputs (
"\n"
"If '<dimacs>' is missing then the solver reads from '<stdin>',\n"
"also if '-' is used as input path name '<dimacs>'.  Similarly,\n"
"if '-' is specified as '<proof>' path then a proof is generated\n"
"and printed to '<stdout>'.\n"
"\n"
"By default the proof is stored in the binary DRAT format unless\n"
"the option '--no-binary' is specified or the proof is written\n"
"to  '<stdout>' and '<stdout>' is connected to a terminal.\n"
"\n"
"The input is assumed to be compressed if it is given explicitly\n"
"and has a '.gz', '.bz2', '.xz' or '.7z' suffix.  The same applies\n"
"to the output file.  In order to use compression and decompression\n"
"the corresponding utilities 'gzip', 'bzip', 'xz', and '7z' (depending\n"
"on the format) are required and need to be installed on the system.\n",
    stdout);
  }
}

/*------------------------------------------------------------------------*/

// Pretty print competition format witness with 'v' lines.
//
void App::print_witness (FILE * file) {
  int c = 0, i = 0, tmp;
  do {
    if (!c) fputc ('v', file), c = 1;
    if (i++ == max_var) tmp = 0;
    else tmp = solver->val (i) < 0 ? -i : i;
    char str[20];
    sprintf (str, " %d", tmp);
    int l = strlen (str);
    if (c + l > 78) fputs ("\nv", file), c = 1;
    fputs (str, file);
    c += l;
  } while (tmp);
  if (c) fputc ('\n', file);
}

/*------------------------------------------------------------------------*/

// Wrapper around option setting.

int App::get (const char * o) { return solver->get (o); }
bool App::set (const char * o, int v) { return solver->set (o, v); }
bool App::set (const char * arg) { return solver->set_long_option (arg); }

/*------------------------------------------------------------------------*/

// Short-cut for errors to avoid a hard 'exit'.

#define APPERR(...) \
do { solver->error (__VA_ARGS__); } while (0)

/*------------------------------------------------------------------------*/

int App::main (int argc, char ** argv) {
  const char * proof_path = 0, * solution_path = 0, * dimacs_path = 0;
  const char * output_path = 0, * extension_path = 0, * config = 0;
  int i, res = 0, optimize = 0, preprocessing = 0, localsearch = 0;
  bool proof_specified = false, dimacs_specified = false;
  int conflict_limit = -1, decision_limit = -1;
  bool witness = true, less = false;
  const char * dimacs_name, * err;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "-h")) {
      print_usage ();
      return 0;
    } else if (!strcmp (argv[i], "--help")) {
      print_usage (true);
      return 0;
    } else if (!strcmp (argv[i], "--version")) {
      printf ("%s\n", CaDiCaL::version ());
      return 0;
    } else if (!strcmp (argv[i], "--build")) {
      tout.disable ();
      Solver::build (stdout, "");
      return 0;
    } else if (!strcmp (argv[i], "--copyright")) {
      printf ("%s\n", copyright ());
      return 0;
    } else if (!strcmp (argv[i], "-")) {
      if (proof_specified) APPERR ("too many arguments");
      else if (!dimacs_specified) dimacs_specified = true;
      else                         proof_specified = true;
    } else if (!strcmp (argv[i], "-s")) {
      if (++i == argc) APPERR ("argument to '-s' missing");
      else if (solution_path)
        APPERR ("multiple solution file options '-s %s' and '-s %s'",
          solution_path, argv[i]);
      else solution_path = argv[i];
    } else if (!strcmp (argv[i], "-o")) {
      if (++i == argc) APPERR ("argument to '-o' missing");
      else if (output_path)
        APPERR ("multiple output file options '-o %s' and '-o %s'",
          output_path, argv[i]);
      else if (!File::writable (argv[i]))
        APPERR ("output file '%s' not writable", argv[i]);
      else output_path = argv[i];
    } else if (!strcmp (argv[i], "-e")) {
      if (++i == argc) APPERR ("argument to '-e' missing");
      else if (extension_path)
        APPERR ("multiple extension file options '-e %s' and '-e %s'",
          extension_path, argv[i]);
      else if (!File::writable (argv[i]))
        APPERR ("extension file '%s' not writable", argv[i]);
      else extension_path = argv[i];
    } else if (is_color_option (argv[i])) {
      tout.force_colors ();
      terr.force_colors ();
    } else if (is_no_color_option (argv[i])) {
      tout.force_no_colors ();
      terr.force_no_colors ();
    } else if (!strcmp (argv[i], "--witness") ||
               !strcmp (argv[i], "--witness=true") ||
               !strcmp (argv[i], "--witness=1"))
      witness = true;
    else if (!strcmp (argv[i], "-n") ||
             !strcmp (argv[i], "--no-witness") ||
             !strcmp (argv[i], "--witness=false") ||
             !strcmp (argv[i], "--witness=0"))
      witness = false;
    else if (!strcmp (argv[i], "--less")) {             // EXPERIMENTAL!
      if (less) APPERR ("multiple '--less' options");
      else if (!isatty (1))
        APPERR ("'--less' without '<stdout>' connected to terminal");
      else less = true;
    } else if (!strcmp (argv[i], "-c")) {
      if (++i == argc) APPERR ("argument to '-c' missing");
      else if (conflict_limit >= 0)
        APPERR ("multiple conflict limit options '-c %d' and '-c %s'",
          conflict_limit, argv[i]);
      else if (!parse_int_str (argv[i], conflict_limit))
        APPERR ("invalid argument in '-c %s'", argv[i]);
      else if (conflict_limit < 0)
        APPERR ("invalid conflict limit");
    } else if (!strcmp (argv[i], "-d")) {
      if (++i == argc) APPERR ("argument to '-d' missing");
      else if (decision_limit >= 0)
        APPERR ("multiple decision limit options '-d %d' and '-d %s'",
          decision_limit, argv[i]);
      else if (!parse_int_str (argv[i], decision_limit))
        APPERR ("invalid argument in '-d %s'", argv[i]);
      else if (decision_limit < 0)
        APPERR ("invalid decision limit");
    } else if (!strcmp (argv[i], "-t")) {
      if (++i == argc) APPERR ("argument to '-t' missing");
      else if (time_limit >= 0)
        APPERR ("multiple time limit options '-t %d' and '-t %s'",
          time_limit, argv[i]);
      else if (!parse_int_str (argv[i], time_limit))
        APPERR ("invalid argument in '-d %s'", argv[i]);
      else if (time_limit < 0)
        APPERR ("invalid time limit");
    }
#ifndef QUIET
    else if (!strcmp (argv[i], "-q")) set ("--quiet");
    else if (!strcmp (argv[i], "-v"))
      solver->set ("verbose", get ("verbose") + 1);
#endif
#ifdef LOGGING
    else if (!strcmp (argv[i], "-l")) set ("--log");
#endif
    else if (!strcmp (argv[i], "-f") ||
             !strcmp (argv[i], "--force") ||
             !strcmp (argv[i], "--force=1") ||
             !strcmp (argv[i], "--force=true")) strict = 0;
    else if (!strcmp (argv[i], "--strict") ||
             !strcmp (argv[i], "--strict=1") ||
             !strcmp (argv[i], "--strict=true")) strict = 2;
    else if (argv[i][0] == '-' && argv[i][1] == 'O') {
      if (!parse_int_str (argv[i] + 2, optimize) ||
          optimize < 0 || optimize > 31)
        APPERR ("invalid optimization option '%s' (expected '-O[0..31]')",
          argv[i]);
    } else if (argv[i][0] == '-' && argv[i][1] == 'P') {
      if (!parse_int_str (argv[i] + 2, preprocessing) || preprocessing < 0)
        APPERR ("invalid preprocessing option '%s' (expected '-P<int>')",
          argv[i]);
    } else if (argv[i][0] == '-' && argv[i][1] == 'L') {
      if (!parse_int_str (argv[i] + 2, localsearch) || localsearch < 0)
        APPERR ("invalid local search option '%s' (expected '-L<int>')",
          argv[i]);
    } else if (argv[i][0] == '-' && argv[i][1] == '-' &&
               solver->is_valid_configuration (argv[i] + 2)) {
      if (config)
         APPERR ("can not use two configurations '--%s' and '%s'",
           config, argv[i]);
      config = argv[i] + 2;
    } else if (set (argv[i])) { /* nothing do be done */ }
    else if (argv[i][0] == '-') APPERR ("invalid option '%s'", argv[i]);
    else if (proof_specified) APPERR ("too many arguments");
    else if (dimacs_specified) {
      if (!File::writable (argv[i]))
        APPERR ("DRAT proof file '%s' not writable", argv[i]);
      proof_specified = true;
      proof_path = argv[i];
    } else dimacs_specified = true, dimacs_path = argv[i];
  }

  // The '--less' option is not fully functional yet.  It only works as
  // expected if you let the solver run until it exits.  The goal is to have
  // a similar experience as the default with 'git diff' if the terminal is
  // too small for the message.
  //
  // TODO: add proper forking, waiting, signal catching & propagating ...
  //
  FILE * less_pipe;
  if (less) {
    assert (isatty (1));
    less_pipe = popen ("less -r", "w");
    if (!less_pipe)
      APPERR ("could not execute and open pipe to 'less -r' command");
    dup2 (fileno (less_pipe), 1);
  } else less_pipe = 0;

  if (dimacs_specified && dimacs_path && !File::exists (dimacs_path))
    APPERR ("DIMACS input file '%s' does not exist", dimacs_path);
  if (solution_path && !File::exists (solution_path))
    APPERR ("solution file '%s' does not exist", solution_path);
  if (dimacs_specified && dimacs_path &&
      proof_specified && proof_path &&
      !strcmp (dimacs_path, proof_path) && strcmp (dimacs_path, "-"))
    APPERR ("DIMACS input file '%s' also specified as DRAT proof file",
      dimacs_path);
  if (solution_path && !get ("check")) set ("--check");
#ifndef QUIET
  if (!get ("quiet")) {
    solver->section ("banner");
    solver->message ("%sCaDiCaL Radically Simplified CDCL SAT Solver%s",
      tout.bright_magenta_code (), tout.normal_code ());
    solver->message ("%s%s%s",
      tout.bright_magenta_code (), copyright (), tout.normal_code ());
    solver->message ();
    CaDiCaL::Solver::build (stdout, "c ");
  }
#endif
  if (config) {
    solver->section ("config");
    assert (Config::has (config));
    solver->message ("using '%s' configuration (%s)",
      config, Config::description (config));
    solver->configure (config);
  }
  if (preprocessing > 0 || localsearch > 0 ||
      time_limit >= 0 || conflict_limit >= 0 || decision_limit >= 0) {
    solver->section ("limit");
    if (preprocessing > 0) {
      solver->message (
        "enabling %d initial rounds of preprocessing", preprocessing);
      solver->limit ("preprocessing", preprocessing);
    }
    if (localsearch > 0) {
      solver->message (
        "enabling %d initial rounds of local search", localsearch);
      solver->limit ("localsearch", localsearch);
    }
    if (time_limit >= 0) {
      solver->message (
        "setting time limit to %d seconds real time",
        time_limit);
      Signal::alarm (time_limit);
      solver->connect_terminator (this);
    }
    if (conflict_limit >= 0) {
      solver->message ("setting conflict limit to %d conflicts",
        conflict_limit);
      bool succeeded = solver->limit ("conflicts", conflict_limit);
      assert (succeeded), (void) succeeded;
    }
    if (decision_limit >= 0) {
      solver->message ("setting decision limit to %d decisions",
        decision_limit);
      bool succeeded = solver->limit ("decisions", decision_limit);
      assert (succeeded), (void) succeeded;
    }
  }
  if (verbose () || proof_specified) solver->section ("proof tracing");
  if (proof_specified) {
    if (!proof_path) {
      const bool force_binary = (isatty (1) && get ("binary"));
      if (force_binary) set ("--no-binary");
      solver->message ("writing %s proof trace to %s'<stdout>'%s",
        (get ("binary") ? "binary" : "non-binary"),
        tout.green_code (), tout.normal_code ());
      if (force_binary)
        solver->message (
          "connected to terminal thus non-binary proof forced");
      solver->trace_proof (stdout, "<stdout>");
    } else if (!solver->trace_proof (proof_path))
      APPERR ("can not open and write DRAT proof to '%s'", proof_path);
    else
      solver->message (
        "writing %s proof trace to %s'%s'%s",
        (get ("binary") ? "binary" : "non-binary"),
        tout.green_code (), proof_path, tout.normal_code ());
  } else solver->verbose (1, "will not generate nor write DRAT proof");
  solver->section ("parsing input");
  dimacs_name = dimacs_path ? dimacs_path : "<stdin>";
  string help;
  if (!dimacs_path) {
    help += " ";
    help += tout.magenta_code ();
    help += "(use '-h' for a list of common options)";
    help += tout.normal_code ();
  }
  solver->message ("reading DIMACS file from %s'%s'%s%s",
    tout.green_code (), dimacs_name, tout.normal_code (), help.c_str ());
  if (dimacs_path)
       err = solver->read_dimacs (dimacs_path, max_var, strict);
  else err = solver->read_dimacs (stdin, dimacs_name, max_var, strict);
  if (err) APPERR ("%s", err);
  if (solution_path) {
    solver->section ("parsing solution");
    solver->message ("reading solution file from '%s'", solution_path);
    if ((err = solver->read_solution (solution_path)))
      APPERR ("%s", err);
  }

  solver->section ("options");
  if (optimize > 0) {
    solver->optimize (optimize);
    solver->message ();
  }
  solver->options ();

  solver->section ("solving");
  res = solver->solve ();

  if (proof_specified) {
    solver->section ("closing proof");
    solver->flush_proof_trace ();
    solver->close_proof_trace ();
  }

  if (output_path) {
    solver->section ("writing output");
    solver->message ("writing simplified CNF to DIMACS file %s'%s'%s",
      tout.green_code (), output_path, tout.normal_code ());
    err = solver->write_dimacs (output_path, max_var);
    if (err) APPERR ("%s", err);
  }

  if (extension_path) {
    solver->section ("writing extension");
    solver->message ("writing extension stack to %s'%s'%s",
      tout.green_code (), extension_path, tout.normal_code ());
    err = solver->write_extension (extension_path);
    if (err) APPERR ("%s", err);
  }

  solver->section ("result");
  if (res == 10) {
    printf ("s SATISFIABLE\n");
    if (witness) {
      fflush (stdout);
      print_witness (stdout);
    }
  } else if (res == 20) printf ("s UNSATISFIABLE\n");
  else printf ("c UNKNOWN\n");
  fflush (stdout);
  solver->statistics ();
  solver->section ("shutting down");
  solver->message ("exit %d", res);
  if (less_pipe) {
    close (1);
    pclose (less_pipe);
  }
  return res;
}

App::App () :
  time_limit (-1), max_var (0), strict (1), timesup (false)
{
  CaDiCaL::Options::report_default_value = 1;
  solver = new Solver;
  Signal::set (this);
}

App::~App () {
  Signal::reset ();
  delete solver;
}

#ifndef QUIET

void App::signal_message (const char * msg, int sig) {
  solver->message (
    "%s%s %ssignal %d%s (%s)%s",
    tout.red_code (), msg,
    tout.bright_red_code (), sig,
    tout.red_code (), Signal::name (sig),
    tout.normal_code ());
}

#endif

void App::catch_signal (int sig) {
#ifndef QUIET
  if (!get ("quiet")) {
    solver->message ();
    signal_message ("caught", sig);
    solver->section ("result");
    solver->message ("UNKNOWN");
    solver->statistics ();
    solver->message ();
    signal_message ("raising", sig);
  }
#else
  (void) sig;
#endif
}

void App::catch_alarm () {

  // Both approaches work. We keep them here for illustration purposes.
  //
  // solver->terminate (); // immediate asynchronous call into solver
  timesup = true;          // wait for solver to call 'App::terminate ()'
}

} // end of 'namespace CaDiCaL'

int main (int argc, char ** argv) {
  CaDiCaL::App app;
  return app.main (argc, argv);
}
