#include "internal.hpp"

/*------------------------------------------------------------------------*/

// This is pretty Linux specific code for resource usage and limits.

// TODO: port these functions to different OS (Windows + MacOS).

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

uint64_t maximum_resident_set_size () {
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  return ((uint64_t) u.ru_maxrss) << 10;
}

// Unfortunately 'getrusage' on Linux does not support current resident set
// size (the field 'ru_ixrss' is there but according to the man page
// 'unused'). Thus we fall back to use the '/proc' file system instead.  So
// this is not portable at all and needs to be replaced on other systems
// The code would still compile though (assuming 'sysconf' and
// '_SC_PAGESIZE' are available).

uint64_t current_resident_set_size () {
  char path[40];
  sprintf (path, "/proc/%" PRId64 "/statm", (int64_t) getpid ());
  FILE * file = fopen (path, "r");
  if (!file) return 0;
  uint64_t dummy, rss;
  int scanned = fscanf (file, "%" PRIu64 " %" PRIu64 "", &dummy, &rss);
  fclose (file);
  return scanned == 2 ? rss * sysconf (_SC_PAGESIZE) : 0;
}

/*------------------------------------------------------------------------*/

// Compiled in assumed default number of core.
//
static const int NUM_CORES = 4;

// Try to obtain the number of cores.
//
int number_of_cores (Internal * internal)
{
#ifdef QUIET
  (void) internal;
#endif

  bool amd, intel, res;

  const int syscores = sysconf (_SC_NPROCESSORS_ONLN);
  if (syscores > 0) MSG ("'sysconf' reports %d processors", syscores);
  else MSG ("'sysconf' fails to determine number of online processors");

  FILE * p = popen (
               "grep '^core id' /proc/cpuinfo 2>/dev/null|sort|uniq|wc -l",
               "r");
  int coreids;
  if (p) {
    if (fscanf (p, "%d", &coreids) != 1) coreids = 0;
    if (coreids > 0) MSG ("found %d core ids in '/proc/cpuinfo'", coreids);
    else MSG ("failed to extract core ids from '/proc/cpuinfo'");
    pclose (p);
  } else coreids = 0;

  p = popen (
        "grep '^physical id' /proc/cpuinfo 2>/dev/null|sort|uniq|wc -l",
        "r");
  int physids;
  if (p) {
    if (fscanf (p, "%d", &physids) != 1) physids = 0;
    if (physids > 0)
         MSG ("found %d physical ids in '/proc/cpuinfo'", physids);
    else MSG ("failed to extract physical ids from '/proc/cpuinfo'");
    pclose (p);
  } else physids = 0;

  int procpuinfocores;
  if (coreids > 0 && physids > 0 &&
      (procpuinfocores = coreids * physids) > 0) {
    MSG ("%d cores = %d core times %d physical ids in '/proc/cpuinfo'",
         procpuinfocores, coreids, physids);
  } else procpuinfocores = 0;

  bool usesyscores = false, useprocpuinfo = false;

  if (procpuinfocores > 0 && procpuinfocores == syscores) {
    MSG ("'sysconf' and '/proc/cpuinfo' results match");
    usesyscores = 1;
  } else if (procpuinfocores > 0 && syscores <= 0) {
    MSG ("only '/proc/cpuinfo' result valid");
    useprocpuinfo = 1;
  } else if (procpuinfocores <= 0 && syscores > 0) {
    MSG ("only 'sysconf' result valid");
    usesyscores = 1;
  } else if (procpuinfocores > 0 && syscores > 0) {
    intel = !system ("grep vendor /proc/cpuinfo 2>/dev/null|grep -q Intel");
    if (intel) MSG ("found Intel as vendor in '/proc/cpuinfo'");
    amd = !system ("grep vendor /proc/cpuinfo 2>/dev/null|grep -q AMD");
    if (amd) MSG ("found AMD as vendor in '/proc/cpuinfo'");
    assert (syscores > 0);
    assert (procpuinfocores > 0);
    assert (syscores != procpuinfocores);
    if (amd) {
      MSG ("trusting 'sysconf' on AMD");
      usesyscores = true;
    } else if (intel) {
      MSG ("'sysconf' result off by a factor of %f on Intel",
           syscores / (double) procpuinfocores);
      MSG ("trusting '/proc/cpuinfo' on Intel");
      useprocpuinfo = true;
    }  else {
      MSG ("trusting 'sysconf' on unknown vendor machine");
      usesyscores = true;
    }
  }

  if (useprocpuinfo) {
    MSG (
      "assuming cores = core * physical ids in '/proc/cpuinfo' = %d",
      procpuinfocores);
    res = procpuinfocores;
  } else if (usesyscores) {
    MSG (
      "assuming cores = number of processors reported by 'sysconf' = %d",
      syscores);
    res = syscores;
  } else {
    MSG (
      "falling back to compiled in default value of %d number of cores",
      NUM_CORES);
    res = NUM_CORES;
  }

  return res;
}

/*------------------------------------------------------------------------*/

static const unsigned MAX_GB = 7;

uint64_t memory_limit (Internal * internal) {
#ifdef QUIET
  (void) internal;
#endif
  uint64_t res;
  FILE * p = popen ("grep MemTotal /proc/meminfo", "r");
  if (p && fscanf (p, "MemTotal: %" PRIu64 " kB", &res) == 1) {
    MSG ("%" PRIu64 " KB total memory according to '/proc/meminfo'", res);
    res <<= 10;
  } else {
    res = ((uint64_t) MAX_GB) << 30;;
    MSG ("assuming compiled in memory limit of %u GB", MAX_GB);
  }
  if (p) pclose (p);
  return res;
}

}
