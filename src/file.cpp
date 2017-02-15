#include "internal.hpp"

/*------------------------------------------------------------------------*/

// Some more low-level 'C' headers.

extern "C" {
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <stdlib.h>
};

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Private constructor.

File::File (Internal *i, bool w, int c, FILE * f, const char * n)
:
  internal (i), writing (w),
  close_file (c), file (f),
  _name (n), _lineno (1), _bytes (0)
{
  assert (f), assert (n);
}

/*------------------------------------------------------------------------*/

bool File::exists (const char * path) {
  struct stat buf;
  return !stat (path, &buf);
}

size_t File::size (const char * path) {
  struct stat buf;
  if (stat (path, &buf)) return 0;
  return (size_t) buf.st_size;
}

// Check that 'prg' is in the 'PATH' and thus can be found if executed
// through 'popen'.

char * File::find (const char * prg) {
  size_t prglen = strlen (prg);
  const char * c = getenv ("PATH");
  if (!c) return 0;;
  size_t len = strlen (c);
  char * e = new char[len + 1];
  strcpy (e, c);
  char * res = 0;
  for (char * p = e, * q; !res && p < e + len; p = q) {
    for (q = p; *q && *q != ':'; q++)
      ;
    *q++ = 0;
    size_t pathlen = (q - p) + prglen;
    char * path = new char [pathlen + 1];
    sprintf (path, "%s/%s", p, prg);
    assert (strlen (path) == pathlen);
    if (exists (path)) res = path;
    else delete [] path;
  }
  delete [] e;
  return res;
}

/*------------------------------------------------------------------------*/

FILE * File::open_file (Internal * internal, const char * path,
                                             const char * mode) {
  return fopen (path, mode);
}

FILE * File::read_file (Internal * internal, const char * path) {
  MSG ("opening file to read '%s'", path);
  return open_file (internal, path, "r");
}

FILE * File::write_file (Internal * internal, const char * path) {
  MSG ("opening file to write '%s'", path);
  return open_file (internal, path, "w");
}

/*------------------------------------------------------------------------*/

FILE * File::open_pipe (Internal * internal,
                        const char * fmt, const char * path,
                        const char * mode) {
  size_t prglen = 0;
  while (fmt[prglen] && fmt[prglen] != ' ') prglen++;
  char * prg = new char [prglen + 1];
  strncpy (prg, fmt, prglen);
  prg[prglen] = 0;
  char * found = find (prg);
  if (found) MSG ("found '%s' in path for '%s'", found, prg);
  delete [] prg;
  if (!found) return 0;
  delete [] found;
  char * cmd = new char [strlen (fmt) + strlen (path)];
  sprintf (cmd, fmt, path);
  FILE * res = popen (cmd, mode);
  delete [] cmd;
  return res;
}

FILE * File::read_pipe (Internal * internal,
                        const char * fmt, const char * path) {
  if (!File::exists (path)) return 0;
  MSG ("opening pipe to read '%s'", path);
  return open_pipe (internal, fmt, path, "r");
}

FILE * File::write_pipe (Internal * internal,
                         const char * fmt, const char * path) {
  MSG ("opening pipe to write '%s'", path);
  return open_pipe (internal, fmt, path, "w");
}

/*------------------------------------------------------------------------*/

File * File::read (Internal * internal, FILE * f, const char * n) {
  return new File (internal, false, 0, f, n);
}

File * File::write (Internal * internal, FILE * f, const char * n) {
  return new File (internal, true, 0, f, n);
}

File * File::read (Internal * internal, const char * path) {
  FILE * file;
  int close_input = 2;
  if (has_suffix (path, ".xz"))
    file = read_pipe (internal, "xz -c -d %s", path);
  else if (has_suffix (path, ".bz2"))
    file = read_pipe (internal, "bzip2 -c -d %s", path);
  else if (has_suffix (path, ".gz"))
    file = read_pipe (internal, "gzip -c -d %s", path);
  else if (has_suffix (path, ".7z"))
    file = read_pipe (internal, "7z x -so %s 2>/dev/null", path);
  else
    file = read_file (internal, path), close_input = 1;
  return file ? new File (internal, false, close_input, file, path) : 0;
}

File * File::write (Internal * internal, const char * path) {
  FILE * file;
  int close_input = 2;
  if (has_suffix (path, ".xz"))
    file = write_pipe (internal, "xz -c > %s", path);
  else if (has_suffix (path, ".bz2"))
    file = write_pipe (internal, "bzip2 -c > %s", path);
  else if (has_suffix (path, ".gz"))
    file = write_pipe (internal, "gzip -c > %s", path);
  else if (has_suffix (path, ".7z"))
    file = write_pipe (internal,
                       "7z a -an -txz -si -so > %s 2>/dev/null", path);
  else
    file = write_file (internal, path), close_input = 1;
  return file ? new File (internal, true, close_input, file, path) : 0;
}

File::~File () {
  if (close_file == 1) {
    MSG ("closing file '%s'", name ());
    fclose (file);
  }
  if (close_file == 2) {
    MSG ("closing pipe command on '%s'", name ());
    pclose (file);
  }
#ifndef QUIET
  double mb = bytes () / (double) (1 << 20);
  if (writing) MSG ("after writing %ld bytes %.1f MB", bytes (), mb);
  else MSG ("after reading %ld bytes %.1f MB", bytes (), mb);
  if (close_file == 2) {
    long s = size (name ());
    double mb = s / (double) (1<<20);
    if (writing)
      MSG ("deflated to %ld bytes %.1f MB by factor %.2f (%.2f%% compression)",
        s, mb, relative (bytes (), s), percent (bytes () - s, bytes ()));
    else
      MSG ("inflated from %ld bytes %.1f MB by factor %.2f (%.2f%% compression)",
        s, mb, relative (bytes (), s), percent (bytes () - s, bytes ()));
  }
#endif
}

};
