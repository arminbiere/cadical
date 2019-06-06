#ifndef _config_hpp_INCLUDED
#define _config_hpp_INCLUDED

namespace CaDiCaL {

class Options;

namespace Config {
  bool has (const char *);
  const char * description (const char *);
  bool set (Solver &, const char *);
  void usage ();
}

}

#endif
