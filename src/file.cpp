#include "internal.hpp"
#include "util.hpp"

/*------------------------------------------------------------------------*/

// Some more low-level 'C' headers.

extern "C" {
#include <errno.h>
#include <fcntl.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
}

#if defined(__APPLE__) || defined(__MACH__)

extern "C" {
#include <libproc.h>
#include <sys/proc_info.h>
}

#include <mutex>

#endif

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Private constructor.

File::File (Internal *i, bool w, int c, FILE *f, const char *n)
    : internal (i),
#if !defined(QUIET) || !defined(NDEBUG)
      writing (w),
#endif
      close_file (c), file (f), _name (strdup (n)), _lineno (1),
      _bytes (0) {
  (void) w;
  assert (f), assert (n);
}

/*------------------------------------------------------------------------*/

bool File::exists (const char *path) {
  struct stat buf;
  if (stat (path, &buf))
    return false;
  if (access (path, R_OK))
    return false;
  return true;
}

bool File::writable (const char *path) {
  int res;
  if (!path)
    res = 1;
  else if (!strcmp (path, "/dev/null"))
    res = 0;
  else {
    if (!*path)
      res = 2;
    else {
      struct stat buf;
      const char *p = strrchr (path, '/');
      if (!p) {
        if (stat (path, &buf))
          res = ((errno == ENOENT) ? 0 : -2);
        else if (S_ISDIR (buf.st_mode))
          res = 3;
        else
          res = (access (path, W_OK) ? 4 : 0);
      } else if (!p[1])
        res = 5;
      else {
        size_t len = p - path;
        char *dirname = new char[len + 1];
        strncpy (dirname, path, len);
        dirname[len] = 0;
        if (stat (dirname, &buf))
          res = 6;
        else if (!S_ISDIR (buf.st_mode))
          res = 7;
        else if (access (dirname, W_OK))
          res = 8;
        else if (stat (path, &buf))
          res = (errno == ENOENT) ? 0 : -3;
        else
          res = access (path, W_OK) ? 9 : 0;
        delete[] dirname;
      }
    }
  }
  return !res;
}

bool File::piping () {
  struct stat stat;
  int fd = fileno (file);
  if (fstat (fd, &stat))
    return true;
  return S_ISFIFO (stat.st_mode);
}

// These are signatures for supported compressed file types.  In 2018 the
// SAT Competition was running on StarExec and used internally 'bzip2'
// compressed files, but gave them uncompressed to the solver using exactly
// the same path (with '.bz2' suffix).  Then 'CaDiCaL' tried to read that
// actually uncompressed file through 'bzip2', which of course failed.  Now
// we double check and fall back to reading the file as is, if the signature
// does not match after issuing a warning.

static const int xzsig[] = {0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, EOF};
static const int bz2sig[] = {0x42, 0x5A, 0x68, EOF};
static const int gzsig[] = {0x1F, 0x8B, EOF};
static const int sig7z[] = {0x37, 0x7A, 0xBC, 0xAF, 0x27, 0x1C, EOF};
static const int lzmasig[] = {0x5D, EOF};

bool File::match (Internal *internal, const char *path, const int *sig) {
  assert (path);
  FILE *tmp = fopen (path, "r");
  if (!tmp) {
    WARNING ("failed to open '%s' to check signature", path);
    return false;
  }
  bool res = true;
  for (const int *p = sig; res && (*p != EOF); p++)
    res = (cadical_getc_unlocked (tmp) == *p);
  fclose (tmp);
  if (!res)
    WARNING ("file type signature check for '%s' failed", path);
  return res;
}

size_t File::size (const char *path) {
  struct stat buf;
  if (stat (path, &buf))
    return 0;
  return (size_t) buf.st_size;
}

// Check that 'prg' is in the 'PATH' and thus can be found if executed
// through 'popen' or 'exec'.

char *File::find_program (const char *prg) {
  size_t prglen = strlen (prg);
  const char *c = getenv ("PATH");
  if (!c)
    return 0;
  size_t len = strlen (c);
  char *e = new char[len + 1];
  strcpy (e, c);
  char *res = 0;
  for (char *p = e, *q; !res && p < e + len; p = q) {
    for (q = p; *q && *q != ':'; q++)
      ;
    *q++ = 0;
    size_t pathlen = (q - p) + prglen;
    char *path = new char[pathlen + 1];
    snprintf (path, pathlen + 1, "%s/%s", p, prg);
    assert (strlen (path) == pathlen);
    if (exists (path))
      res = path;
    else
      delete[] path;
  }
  delete[] e;
  return res;
}

/*------------------------------------------------------------------------*/

FILE *File::open_file (Internal *internal, const char *path,
                       const char *mode) {
  (void) internal;
  return fopen (path, mode);
}

FILE *File::read_file (Internal *internal, const char *path) {
  MSG ("opening file to read '%s'", path);
  return open_file (internal, path, "r");
}

FILE *File::write_file (Internal *internal, const char *path) {
  MSG ("opening file to write '%s'", path);
  return open_file (internal, path, "wb");
}

/*------------------------------------------------------------------------*/

void File::split_str (const char *command, std::vector<char *> &argv) {
  const char *c = command;
  while (*c && *c == ' ')
    c++;
  while (*c) {
    const char *p = c;
    while (*p && *p != ' ')
      p++;
    const size_t bytes = p - c;
    char *arg = new char[bytes + 1];
    (void) strncpy (arg, c, bytes);
    arg[bytes] = 0;
    argv.push_back (arg);
    while (*p && *p == ' ')
      p++;
    c = p;
  }
}

void File::delete_str_vector (std::vector<char *> &argv) {
  for (auto str : argv)
    delete[] str;
}

FILE *File::read_pipe (Internal *internal, const char *fmt, const int *sig,
                       const char *path) {
  if (!File::exists (path)) {
    LOG ("file '%s' does not exist", path);
    return 0;
  }
  LOG ("file '%s' exists", path);
  if (sig && !File::match (internal, path, sig))
    return 0;
  LOG ("file '%s' matches signature for '%s'", path, fmt);
  MSG ("opening pipe to read '%s'", path);
  size_t prglen = 0;
  while (fmt[prglen] && fmt[prglen] != ' ')
    prglen++;
  char *prg = new char[prglen + 1];
  strncpy (prg, fmt, prglen);
  prg[prglen] = 0;
  char *found = find_program (prg);
  if (found)
    MSG ("found '%s' in path for '%s'", found, prg);
  if (!found)
    MSG ("did not find '%s' in path", prg);
  delete[] prg;
  if (!found)
    return 0;
  delete[] found;
  size_t cmd_size = strlen (fmt) + strlen (path);
  char *cmd = new char[cmd_size];
  snprintf (cmd, cmd_size, fmt, path);
  FILE *res = popen (cmd, "r");
  delete[] cmd;
  return res;
}

/*------------------------------------------------------------------------*/

File *File::read (Internal *internal, FILE *f, const char *n) {
  return new File (internal, false, 0, f, n);
}

File *File::write (Internal *internal, FILE *f, const char *n) {
  return new File (internal, true, 0, f, n);
}

File *File::read (Internal *internal, const char *path) {
  FILE *file;
  int close_input = 2;
  if (has_suffix (path, ".xz")) {
    file = read_pipe (internal, "xz -c -d %s", xzsig, path);
    if (!file)
      goto READ_FILE;
  } else if (has_suffix (path, ".lzma")) {
    file = read_pipe (internal, "lzma -c -d %s", lzmasig, path);
    if (!file)
      goto READ_FILE;
  } else if (has_suffix (path, ".bz2")) {
    file = read_pipe (internal, "bzip2 -c -d %s", bz2sig, path);
    if (!file)
      goto READ_FILE;
  } else if (has_suffix (path, ".gz")) {
    file = read_pipe (internal, "gzip -c -d %s", gzsig, path);
    if (!file)
      goto READ_FILE;
  } else if (has_suffix (path, ".7z")) {
    file = read_pipe (internal, "7z x -so %s 2>/dev/null", sig7z, path);
    if (!file)
      goto READ_FILE;
  } else {
  READ_FILE:
    file = read_file (internal, path);
    close_input = 1;
  }

  if (!file)
    return 0;
  DeferCloseFile<FILE> delete_file ((FILE *) file);
  File *internal_file = new File (internal, false, close_input, file, path);
  delete_file.release ();
  return internal_file;
}

File *File::write (Internal *internal, const char *path) {
  FILE *file;
  int close_output = 1;
  file = write_file (internal, path);
  if (!file)
    return 0;
  DeferCloseFile<FILE> delete_file ((FILE *) file);
  File *internal_file =
      new File (internal, true, close_output, file, path);
  delete_file.release ();
  return internal_file;
}

void File::close (bool print) {
  assert (file);
#ifndef QUIET
  if (internal->opts.quiet)
    print = false;
  else if (internal->opts.verbose > 0)
    print = true;
#endif
  if (close_file == 0) {
    if (print)
      MSG ("disconnecting from '%s'", name ());
  }
  if (close_file == 1) {
    if (print)
      MSG ("closing file '%s'", name ());
    fclose (file);
  }
  if (close_file == 2) {
    if (print)
      MSG ("closing input pipe to read '%s'", name ());
    pclose (file);
  }

  file = 0; // mark as closed

  // TODO what about error checking for 'fclose' or 'pclose'?

#ifndef QUIET
  if (print) {
    if (writing) {
      uint64_t written_bytes = bytes ();
      double written_mb = written_bytes / (double) (1 << 20);
      MSG ("after writing %" PRIu64 " bytes %.1f MB", written_bytes,
           written_mb);
      if (close_file == 3) {
        size_t actual_bytes = size (name ());
        if (actual_bytes) {
          double actual_mb = actual_bytes / (double) (1 << 20);
          MSG ("deflated to %zd bytes %.1f MB", actual_bytes, actual_mb);
          MSG ("factor %.2f (%.2f%% compression)",
               relative (written_bytes, actual_bytes),
               percent (actual_bytes, written_bytes));
        } else
          MSG ("but could not determine actual size of written file");
      }
    } else {
      uint64_t read_bytes = bytes ();
      double read_mb = read_bytes / (double) (1 << 20);
      MSG ("after reading %" PRIu64 " bytes %.1f MB", read_bytes, read_mb);
      if (close_file == 2) {
        size_t actual_bytes = size (name ());
        double actual_mb = actual_bytes / (double) (1 << 20);
        MSG ("inflated from %zd bytes %.1f MB", actual_bytes, actual_mb);
        MSG ("factor %.2f (%.2f%% compression)",
             relative (read_bytes, actual_bytes),
             percent (actual_bytes, read_bytes));
      }
    }
  }
#endif
}

void File::flush () {
  assert (file);
  fflush (file);
}

File::~File () {
  if (file)
    close ();
  free (_name);
}

} // namespace CaDiCaL
