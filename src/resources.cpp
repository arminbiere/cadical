#ifndef QUIET

#include "internal.hpp"

// This is pretty Linux specific code for reporting resource, that is
// time and memory usage and if you can not compile it then just disable
// it by specifying 'quiet', which disables all messages include resource
// usage messages, e.g., with 'configure.sh -q'.

extern "C" {
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <unistd.h>
#include <string.h>
};

namespace CaDiCaL {

// TODO: port these functions to different OS.

// We use 'getrusage' for the next two functions, which is pretty standard
// on Unix but probably not available on Windows etc. For different variants
// of Unix not all fields are meaningful (or even existing).

double process_time () {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;  // user time
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec; // + system time
  return res;
}

// This seems to work on Linux (man page says since Linux 2.6.32).

size_t maximum_resident_set_size () {
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  return ((size_t) u.ru_maxrss) << 10;
}

// Unfortunately 'getrusage' on Linux does not support current resident set
// size (the field 'ru_ixrss' is there but according to the man page
// 'unused'). Thus we fall back to use the '/proc' file system instead.  So
// this is not portable at all and needs to be replaced on other systems
// The code would still compile though (assuming 'sysconf' and
// '_SC_PAGESIZE' are available).

size_t current_resident_set_size () {
  char path[40];
  sprintf (path, "/proc/%ld/statm", (long) getpid ());
  FILE * file = fopen (path, "r");
  if (!file) return 0;
  long dummy, rss;
  int scanned = fscanf (file, "%ld %ld", &dummy, &rss);
  fclose (file);
  return scanned == 2 ? rss * sysconf (_SC_PAGESIZE) : 0;
}

};

#endif // ifndef QUIET
