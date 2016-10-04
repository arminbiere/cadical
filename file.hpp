#ifndef _file_hpp_INCLUDED
#define _file_hpp_INCLUDED

#include <cstdio>
#include <cassert>

namespace CaDiCaL {

struct File {
  bool writing;
  int close_file;
  FILE * file;
  const char * _name;
  long _lineno;

  File (bool, int, FILE *, const char *);

public:

  static File * read (FILE * f, const char * n);
  static File * read (const char * path);

  static File * write (FILE *, const char *);
  static File * write (const char * path);

  ~File ();

  int get () {
    assert (!writing);
    int res = getc (file);
    if (res == '\n') _lineno++;
    return res;
  }

  void put (char c) { assert (writing); (void) putc (c, file); }
  void put (const char * s) { assert (writing); (void) fputs (s, file); }
  void put (int);

  const char * name () const { return _name; }
  long lineno () const { return _lineno; }
};

};

#endif
