#include "internal.hpp"
#include "macros.hpp"
#include "message.hpp"

namespace CaDiCaL {

void Internal::vivify () {
  if (!opts.vivify) return;
  SWITCH_AND_START (search, simplify, vivify);
  flush_redundant_watches ();
  disconnect_watches ();
  connect_watches ();
  report ('v');
  STOP_AND_SWITCH (vivify, simplify, search);
}

};
