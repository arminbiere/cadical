#include "../../src/cadical.hpp"
#include "../../src/file.hpp"
#include "../../src/internal.hpp"

#include <cassert>
#include <cctype>
#include <climits>
#include <cstdint>
#include <iostream>
#include <string>

extern "C" {
#include <pthread.h>
#include <unistd.h>
}

using namespace std;
using namespace CaDiCaL;

static string prefix (const char *tester) {
  string res = "/tmp/cadical-api-test-parcompwrite-";
  res += tester;
  res += "-";
  res += to_string (getpid ());
  return res;
}

static const char *suffix = ".gz";

static string path (const char *tester, unsigned i) {
  return prefix (tester) + "-" + to_string (i) + suffix;
}

static pthread_mutex_t serialize_mutex = PTHREAD_MUTEX_INITIALIZER;

static void lock () {
  if (pthread_mutex_lock (&serialize_mutex))
    perror ("error: pthread_mutex_lock failed");
}

static void unlock () {
  if (pthread_mutex_unlock (&serialize_mutex))
    perror ("error: pthread_mutex_unlock failed");
}

class tester {
  pthread_t thread;
  bool spath_cached = false;
  string spath;

protected:
  unsigned i;

public:
  tester (unsigned j) : i (j) {}
  virtual ~tester () {}
  virtual const char *name () = 0;
  const char *path ();
  void message (const char *);
  virtual void writing () = 0;
  virtual void reading () = 0;
  virtual void write () = 0;
  virtual bool read (unsigned &j) = 0;
  virtual void close () = 0;
  void unlink ();
  void run ();
  void create ();
  void join ();
};

class stdio_tester : public tester {
  FILE *file = 0;

public:
  stdio_tester (unsigned j) : tester (j) {}
  const char *name () override { return "stdio"; }
  void writing () override {
    file = fopen (path (), "w");
    if (!file)
      perror ("error: fopen to write failed"), exit (1);
  }
  void reading () override {
    file = fopen (path (), "r");
    if (!file)
      perror ("error: fopen to read failed"), exit (1);
  }
  void write () override {
    assert (file);
    if (fprintf (file, "%u\n", i) <= 0)
      fprintf (stderr, "error: fprintf failed\n");
  }
  bool read (unsigned &j) override {
    assert (file);
    if (fscanf (file, "%u", &j) <= 0) {
      fprintf (stderr, "error: fscanf failed\n");
      return false;
    }
    return true;
  }
  void close () override {
    if (fclose (file))
      perror ("error: fclose written failed");
  }
};

class cadical_file_tester : public tester {
  File *file = 0;
  Internal *internal;

public:
  cadical_file_tester (unsigned j) : tester (j) {
    internal = new Internal ();
#ifndef QUIET
    internal->opts.verbose = 0;
    internal->opts.quiet = 1;
#endif
  }
  ~cadical_file_tester () { delete internal; }
  const char *name () override { return "cadical-file"; }
  void writing () override {
    file = File::write (internal, path ());
    if (!file)
      fprintf (stderr, "error: 'File::write' failed\n"), exit (1);
  }
  void reading () override {
    file = File::read (internal, path ());
    if (!file)
      fprintf (stderr, "error: File::read failed\n"), exit (1);
  }
  void write () override {
    assert (file);
    if (!file->put ((uint64_t) i) || !file->endl ())
      fprintf (stderr, "error: File::put failed\n");
  }
  bool read (unsigned &j) override {
    assert (file);
    int ch = file->get ();
    if (!isdigit (ch)) {
    INVALID_NUMBER:
      fprintf (stderr,
               "error: invalid number in 'cadical_file_tester::read'\n");
      return false;
    }
    unsigned tmp = ch - '0';
    while (isdigit (ch = file->get ())) {
      if (UINT_MAX / 10 < tmp)
        goto INVALID_NUMBER;
      tmp *= 10;
      unsigned digit = ch - '0';
      if (UINT_MAX - digit < tmp)
        goto INVALID_NUMBER;
      tmp += digit;
    }
    if (ch != '\n') {
      fprintf (stderr, "error: expected new-line after number");
      return false;
    }
    if (file->get () != EOF) {
      fprintf (stderr,
               "error: expected end-of-file after line with number");
      return false;
    }
    j = tmp;
    return true;
  }
  void close () override {
    assert (file);
    file->close ();
  }
};

const char *tester::path () {
  if (!spath_cached) {
    spath = ::path (name (), i);
    spath_cached = true;
  }
  return spath.c_str ();
}

void tester::message (const char *what) {
  lock ();
  printf ("%-17s %s\n", what, path ());
  fflush (stdout);
  unlock ();
}

void tester::run () {
  message ("opening-to-write");
  writing ();
  message ("writing");
  write ();
  message ("closing");
  close ();
  message ("reading");
  reading ();
  unsigned j;
  if (read (j) && i == j)
    message ("checked");
  else {
    lock ();
    fprintf (stderr,
             "error: writing and reading back '%u' from '%s' failed\n", i,
             path ());
    fflush (stderr);
    unlock ();
    exit (1);
  }
  message ("closing");
  close ();
  unlink ();
}

void tester::unlink () {
  message ("deleting");
  if (::unlink (path ()))
    perror ("error: unlink failed");
}

void *start (void *p) {
  tester *t = (tester *) p;
  t->run ();
  return t;
}

void tester::create () {
  if (pthread_create (&thread, 0, start, this))
    perror ("error: 'pthread_created' failed");
}

void tester::join () {
  void *p;
  if (pthread_join (thread, &p))
    perror ("error: 'pthread_join' failed");
  assert (p == this);
}

#include <csignal>

static void catch_alarm (int sig) {
  assert (sig == SIGALRM);
  const char *msg = "error: unexpected alarm (file I/O hanging?)\n";
  if (::write (2, msg, strlen (msg)))
    exit (2);
  (void) sig;
  exit (1);
}

int main () {
  const char *suffixes[] = {"", ".gz"};
  (void) ::signal (SIGALRM, catch_alarm);
  ::alarm (1);
  for (auto s : suffixes) {
    suffix = s;
    for (unsigned c = 0; c != 2; c++) {
      if (!c && *suffix)
        continue;
      vector<tester *> testers;
      for (size_t i = 0; i != 100; i++) {
        tester *t;
        if (c)
          t = new cadical_file_tester (i);
        else
          t = new stdio_tester (i);
        testers.push_back (t);
      }
      for (auto t : testers)
        t->create ();
      for (auto t : testers)
        t->join ();
      for (auto t : testers)
        delete t;
    }
  }
  return 0;
}
