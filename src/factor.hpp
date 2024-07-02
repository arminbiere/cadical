#ifndef _factor_hpp_INCLUDED
#define _factor_hpp_INCLUDED

namespace CaDiCaL {

struct Internal;

struct Factorizor {
  Factorizor () {}
  ~Factorizor () {}
  vector<Clause *> delete_later;
  // TODO schedule
};

} // namespace CaDiCaL

#endif
