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
  // TODO check that file exists and if not return 0
  return open_pipe (fmt, path, "r");
}

static FILE * write_pipe (const char * fmt, const char * path) {
  return open_pipe (fmt, path, "w");
}

File::File (bool w, int c, FILE * f, const char * n) :
#ifndef NDEBUG
  writing (w),
#endif
  close_file (c), file (f), _name (n), _lineno (1)
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
  if (has_suffix (path, ".xz"))
    file = read_pipe ("xz -c -d %s", path);
  else if (has_suffix (path, ".bz2"))
    file = read_pipe ("bunzip2 -c -d %s", path);
  else if (has_suffix (path, ".gz"))
    file = read_pipe ("gzip -c -d %s", path);
  else if (has_suffix (path, ".7z"))
    file = read_pipe ("7z x -so %s 2>/dev/null", path);
  else
    file = fopen (path, "r"), close_input = 1;
  return file ? new File (false, close_input, file, path) : 0;
}

File * File::write (const char * path) {
  FILE * file = fopen (path, "w");
  int close_input = 2;
  if (has_suffix (path, ".xz"))
    file = write_pipe ("xz -c -e > %s", path);
  else if (has_suffix (path, ".bz2"))
    file = write_pipe ("bzip2 -c > %s", path);
  else if (has_suffix (path, ".gz"))
    file = write_pipe ("gzip -c > %s", path);
  else if (has_suffix (path, ".7z"))
    file = write_pipe ("7z a -an -txz -si -so > %s 2>/dev/null", path);
  else
    file = fopen (path, "w"), close_input = 1;
  return file ? new File (true, close_input, file, path) : 0;
}

File::~File () {
  if (close_file == 1) fclose (file);
  if (close_file == 2) pclose (file);
}

};
