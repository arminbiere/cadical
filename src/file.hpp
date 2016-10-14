#ifndef _file_hpp_INCLUDED
#define _file_hpp_INCLUDED

#include <cstdio>
#include <cassert>

namespace CaDiCaL {

// Wraps a 'C' file 'FILE' with name and supports zipped reading and writing
// through 'popen' using external helper tools.  Reading has line numbers.
// Unzipping relies on external utilities, e.g., 'gunzip', 'bzcat' and '7z',
// while zipping relies on 'gzip', 'bzip2' and '7z' as external tools.

class File {

#ifndef NDEBUG
  bool writing;
#endif
  int close_file;
  FILE * file;
  const char * _name;
  long _lineno;

  File (bool, int, FILE *, const char *);

public:

  static File * read (FILE * f, const char * name);
  static File * read (const char * path);

  static File * write (FILE *, const char * name);
  static File * write (const char * path);

  ~File ();

  // Using the 'unlocked' versions here is way faster but
  // not thread safe if the same file is used by different
  // threads, which on the other hand currently is impossible.

  int get () {
    assert (!writing);
    int res = getc_unlocked (file);
    if (res == '\n') _lineno++;
    return res;
  }

  static void print (char ch, FILE * file = stdout) {
    fputc_unlocked (ch, file);
  }

  static void print (unsigned char ch, FILE * file = stdout) {
    fputc_unlocked (ch, file);
  }

  static void print (const char * s, FILE * file = stdout) {
    fputs_unlocked (s, file);
  }

  static void print (int lit, FILE * file = stdout) {
    char buffer[16];
    sprintf (buffer, "%d", lit);        // TODO faster?
    print (buffer, file);
  }

  void put (char c) { assert (writing); print (c, file); }
  void put (unsigned char c) { assert (writing); print (c, file); }
  void put (const char * s) { assert (writing); print (s, file); }
  void put (int lit) { assert (writing); print (lit, file); }

  const char * name () const { return _name; }
  long lineno () const { return _lineno; }
};

};

#endif
