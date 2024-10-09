#include "../../src/cadical.hpp"

#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>

extern "C" {
#include <pthread.h>
#include <unistd.h>
};

using namespace std;

static string prefix (const char *tester) {
  string res = "/tmp/parcompwrite-";
  res += tester;
  res += "-";
  res += to_string (getpid ());
  res += "-";
  return res;
}

static string path (const char *tester, unsigned i) {
  return prefix (tester) + "-" + to_string (i) + ".gz";
}

static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;

static void lock () {
  if (pthread_mutex_lock (&mutex))
    perror ("pthread_mutex_lock failed");
}

static void unlock () {
  if (pthread_mutex_unlock (&mutex))
    perror ("pthread_mutex_unlock failed");
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
      perror ("fopen to write failed"), exit (1);
  }
  void reading () override {
    file = fopen (path (), "r");
    if (!file)
      perror ("fopen to read failed"), exit (1);
  }
  void write () override {
    assert (file);
    if (fprintf (file, "%u\n", i) <= 0)
      fprintf (stderr, "fprintf failed\n");
  }
  bool read (unsigned &j) override {
    assert (file);
    if (fscanf (file, "%u", &j) <= 0) {
      fprintf (stderr, "fscanf failed\n");
      return false;
    }
    return true;
  }
  void close () override {
    if (fclose (file))
      perror ("fclose written failed");
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
    fprintf (stderr, "writing and reading back '%u' from '%s' failed\n", i,
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
    perror ("unlink failed");
}

void *start (void * p) {
  tester *t = (tester*) p;
  t->run ();
  return t;
}

void tester::create () {
  if (pthread_create (&thread, 0, start, this))
    perror ("'pthread_created' failed");
}

void tester::join () {
  void* p;
  if (pthread_join (thread, &p))
    perror ("'pthread_join' failed");
  assert (p == this);
}

int main () {
  vector<tester*> testers;
  for (size_t i = 0; i != 100; i++)
    testers.push_back (new stdio_tester (i));
  for (auto t : testers)
    t->create ();
  for (auto t : testers)
    t->join ();
  for (auto t : testers)
    delete t;
  return 0;
}
