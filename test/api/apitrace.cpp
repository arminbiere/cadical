#include "../../src/cadical.hpp"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <cstdlib>
#include <string>

using namespace std;
using namespace CaDiCaL;

static string path (const char *name) {
  const char *prefix = getenv ("CADICALBUILD");
  string res = prefix ? prefix : ".";
  res += "/test-api-apitrace-";
  res += name;
  res += ".trace";
  return res;
}

static FILE *trace (const char *name) {
  return fopen (path (name).c_str (), "w");
}

int main () {

  {
    FILE *file = trace ("file1");
    {
      Solver solver;
      solver.trace_api_calls (file);
    }
    fclose (file);
  }

  {
    setenv ("CADICAL_API_TRACE", path ("environment1").c_str (), 1);
    {
      Solver solver;
      int var1 = solver.declare_one_more_variable ();
      int var2 = solver.declare_one_more_variable ();
      solver.add (var1);
      solver.add (var2);
      solver.add (0);
      solver.solve ();
    }
    unsetenv ("CADICAL_API_TRACE");
  }

  // For now, when 'factor' is disabled and we do not check for wrong API
  // usage with respect to declared variables, the following two go through.

  {
    FILE *file = trace ("file2");
    {
      Solver solver;
      solver.set ("factor", 0);
      solver.trace_api_calls (file);
      solver.set ("factorcheck", 0);
      solver.add (1);
      solver.add (0);
      solver.add (-1);
      solver.add (0);
      solver.solve ();
    }
    fclose (file);
  }

  {
    setenv ("CADICAL_API_TRACE", path ("environment2").c_str (), 1);
    {
      Solver solver;
      int var1 = solver.declare_one_more_variable ();
      int var2 = solver.declare_one_more_variable ();
      solver.add (-var1);
      solver.add (-var2);
      solver.add (0);
      solver.solve ();
    }
    unsetenv ("CADICAL_API_TRACE");
  }

  return 0;
}
