#include "internal.hpp"

/*------------------------------------------------------------------------*/

// This is pretty Linux specific code for reporting resource usage.
// TODO: port these functions to different OS.

extern "C" {
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <unistd.h>
#include <string.h>
}

namespace CaDiCaL {

double absolute_real_time () {
  struct timeval tv;
  if (gettimeofday (&tv, 0)) return 0;
  return 1e-6 * tv.tv_usec + tv.tv_sec;
}

double Internal::real_time () {
  return absolute_real_time () - stats.time.real;
}

/*------------------------------------------------------------------------*/

// We use 'getrusage' for 'process_time' and 'maximum_resident_set_size'
// which is pretty standard on Unix but probably not available on Windows
// etc.  For different variants of Unix not all fields are meaningful.

double absolute_process_time () {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;  // user time
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec; // + system time
  return res;
}

double Internal::process_time () {
  return absolute_process_time () - stats.time.process;
}

/*------------------------------------------------------------------------*/

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
  sprintf (path, "/proc/%" PRId64 "/statm", (int64_t) getpid ());
  FILE * file = fopen (path, "r");
  if (!file) return 0;
  int64_t dummy, rss;
  int scanned = fscanf (file, "%" PRId64 " %" PRId64 "", &dummy, &rss);
  fclose (file);
  return scanned == 2 ? rss * sysconf (_SC_PAGESIZE) : 0;
}

}
