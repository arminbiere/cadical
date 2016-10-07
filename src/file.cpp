#include "file.hpp"

#include <cstring>

namespace CaDiCaL {

static bool has_suffix (const char * str, const char * suffix) {
  int k = strlen (str), l = strlen (suffix);
  return k > l && !strcmp (str + k - l, suffix);
}

static FILE *
open_pipe (const char * fmt, const char * path, const char * mode) {
  char * cmd = new char [strlen (fmt) + strlen (path)];
  sprintf (cmd, fmt, path);
  FILE * res = popen (cmd, mode);
  delete [] cmd;
  return res;
}

static FILE * read_pipe (const char * fmt, const char * path) {
  return open_pipe (fmt, path, "r");
}

#if 0
static FILE * write_pipe (const char * fmt, const char * path) {
  return open_pipe (fmt, path, "w");
}
#endif

File::File (bool w, int c, FILE * f, const char * n) :
  writing (w), close_file (c), file (f), _name (n), _lineno (0)
{
  assert (f), assert (n);
}

File * File::read (FILE * f, const char * n) {
  return new File (false, 0, f, n);
}

File * File::write (FILE * f, const char * n) {
  return new File (true, 0, f, n);
}

File * File::read (const char * path) {
  FILE * file;
  int close_input = 2;
  if (has_suffix (path, ".bz2"))
    file = read_pipe ("bzcat %s", path);
  else if (has_suffix (path, ".gz"))
    file = read_pipe ("gunzip -c %s", path);
  else if (has_suffix (path, ".7z"))
    file = read_pipe ("7z x -so %s 2>/dev/null", path);
  else
    file = fopen (path, "r"), close_input = 1;
  return file ? new File (false, close_input, file, path) : 0;
}

File * File::write (const char * path) {
  FILE * file = fopen (path, "w");
  return file ? new File (true, 1, file, path) : 0;
}

File::~File () {
  if (close_file == 1) fclose (file);
  if (close_file == 2) pclose (file);
}

};
