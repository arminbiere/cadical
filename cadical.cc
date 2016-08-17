#include <cstdio>

static void msg (const char * fmt, ...) {
  va_list ap;
  fputs ("c ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

#ifdef ENABLE_LOGGING
#define LOG(FMT,ARGS...) do { msg (" LOG " FMT, ##ARGS); } while (0)
#else
#define LOG(ARGS..) do { } while (0)
#endif

static void die (const char * fmt, ...) {
  va_list ap;
  fputs ("*** cadical error: ", stderr);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  exit (1);
}

using namespace std;
#include <vector>

int main () {
}
