#ifndef _file_hpp_INCLUDED
#define _file_hpp_INCLUDED

#include <cstdio>
#include <cassert>
#include <cstdlib>

#ifndef NDEBUG
#include <climits>
#endif

/*------------------------------------------------------------------------*/
#ifndef NUNLOCKED
#define cadical_putc_unlocked putc_unlocked
#define cadical_getc_unlocked getc_unlocked
#else
#define cadical_putc_unlocked putc
#define cadical_getc_unlocked getc
#endif
/*------------------------------------------------------------------------*/

namespace CaDiCaL {

// Wraps a 'C' file 'FILE' with name and supports zipped reading and writing
// through 'popen' using external helper tools.  Reading has line numbers.
// Compression and decompression relies on external utilities, e.g., 'gzip',
// 'bzip2', 'xz', and '7z', which should be in the 'PATH'.

struct Internal;

class File {

#ifndef QUIET
  Internal * internal;
#endif
#if !defined(QUIET) || !defined(NDEBUG)
  bool writing;
#endif

  int close_file;       // need to close file (1=fclose, 2=pclose)
  FILE * file;
  const char * _name;
  uint64_t _lineno;
  uint64_t _bytes;

  File (Internal *, bool, int, FILE *, const char *);

  static FILE * open_file (Internal *,
                           const char * path, const char * mode);
  static FILE * read_file (Internal *, const char * path);
  static FILE * write_file (Internal *, const char * path);

  static FILE * open_pipe (Internal *,
                           const char * fmt,
                           const char * path,
                           const char * mode);
  static FILE * read_pipe (Internal *,
                           const char * fmt,
                           const int * sig,
                           const char * path);
  static FILE * write_pipe (Internal *,
                            const char * fmt, const char * path);
public:

  static char* find (const char * prg);    // search in 'PATH'
  static bool exists (const char * path);  // file exists?
  static bool writable (const char * path);// can write to that file?
  static size_t size (const char * path);  // file size in bytes

  // Does the file match the file type signature.
  //
  static bool match (Internal *, const char * path, const int * sig);

  // Read from existing file. Assume given name.
  //
  static File * read (Internal *, FILE * f, const char * name);

  // Open file from path name for reading (possibly through opening a pipe
  // to a decompression utility, based on the suffix).
  //
  static File * read (Internal *, const char * path);

  // Same for writing as for reading above.
  //
  static File * write (Internal *, FILE *, const char * name);
  static File * write (Internal *, const char * path);

  ~File ();

  // Using the 'unlocked' versions here is way faster but
  // not thread safe if the same file is used by different
  // threads, which on the other hand currently is impossible.

  int get () {
    assert (!writing);
    int res = cadical_getc_unlocked (file);
    if (res == '\n') _lineno++;
    if (res != EOF) _bytes++;
    return res;
  }

  bool put (char ch) {
    assert (writing);
    if (cadical_putc_unlocked (ch, file) == EOF) return false;
    _bytes++;
    return true;
  }

  bool put (unsigned char ch) {
    assert (writing);
    if (cadical_putc_unlocked (ch, file) == EOF) return false;
    _bytes++;
    return true;
  }

  bool put (const char * s) {
    for (const char * p = s; *p; p++)
      if (!put (*p)) return false;
    return true;
  }

  bool put (int lit) {
    assert (writing);
    if (!lit) return put ('0');
    else if (lit == -2147483648) {
      assert (lit == INT_MIN);
      return put ("-2147483648");
    } else {
      char buffer[11];
      int i = sizeof buffer;
      buffer[--i] = 0;
      assert (lit != INT_MIN);
      unsigned idx = abs (lit);
      while (idx) {
        assert (i > 0);
        buffer[--i] = '0' + idx % 10;
        idx /= 10;
      }
      if (lit < 0 && !put ('-')) return false;
      return put (buffer + i);
    }
  }

  bool put (int64_t l) {
    assert (writing);
    if (!l) return put ('0');
    else if (l == INT64_MIN) {
      assert (sizeof l == 8);
      return put ("-9223372036854775808");
    } else {
      char buffer[21];
      int i = sizeof buffer;
      buffer[--i] = 0;
      assert (l != INT64_MIN);
      uint64_t k = l < 0 ? -l : l;
      while (k) {
        assert (i > 0);
        buffer[--i] = '0' + k % 10;
        k /= 10;
      }
      if (l < 0 && !put ('-')) return false;
      return put (buffer + i);
    }
  }

  const char * name () const { return _name; }
  uint64_t lineno () const { return _lineno; }
  uint64_t bytes () const { return _bytes; }

  bool closed () { return !file; }
  void close ();
  void flush ();
};

}

#endif
