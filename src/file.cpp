#include "file.hpp"

extern "C" {
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
};

namespace CaDiCaL {

static bool has_suffix (const char * str, const char * suffix) {
  int k = strlen (str), l = strlen (suffix);
  return k > l && !strcmp (str + k - l, suffix);
}

FILE * File::open_pipe (Internal * internal,
                        const char * fmt, const char * path,
	       	        const char * mode) {
  char * cmd = new char [strlen (fmt) + strlen (path)];
  sprintf (cmd, fmt, path);
  FILE * res = popen (cmd, mode);
  delete [] cmd;
  return res;
}

bool File::exists (const char * path) {
  struct stat buf;
  return !stat (path, &buf);
}

FILE * File::read_pipe (Internal * internal,
                        const char * fmt, const char * path) {
  if (!File::exists (path)) return 0;
  return open_pipe (internal, fmt, path, "r");
}

FILE * File::write_pipe (Internal * internal,
                         const char * fmt, const char * path) {
  return open_pipe (internal, fmt, path, "w");
}

File::File (Internal *i, bool w, int c, FILE * f, const char * n) :
  internal (i), writing (w),
  close_file (c), file (f),
  _name (n), _lineno (1)
{
  assert (f), assert (n);
}

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
    file = fopen (path, "r"), close_input = 1;
  return file ? new File (internal, false, close_input, file, path) : 0;
}

File * File::write (Internal * internal, const char * path) {
  FILE * file = fopen (path, "w");
  int close_input = 2;
  if (has_suffix (path, ".xz"))
    file = write_pipe (internal, "xz -c -e > %s", path);
  else if (has_suffix (path, ".bz2"))
    file = write_pipe (internal, "bzip2 -c > %s", path);
  else if (has_suffix (path, ".gz"))
    file = write_pipe (internal, "gzip -c > %s", path);
  else if (has_suffix (path, ".7z"))
    file = write_pipe (internal,
                       "7z a -an -txz -si -so > %s 2>/dev/null", path);
  else
    file = fopen (path, "w"), close_input = 1;
  return file ? new File (internal, true, close_input, file, path) : 0;
}

File::~File () {
  if (close_file == 1) fclose (file);
  if (close_file == 2) pclose (file);
}

};
