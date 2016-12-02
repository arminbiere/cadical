#if 0
#include "internal.hpp"

namespace CaDiCaL {

void AVG::update (Internal * internal, double y, const char * name) {
  value = count * value + y;
  value /= ++count;
  LOG ("update %s AVG with %g yields %g", name, y, value);
}

};
#endif
