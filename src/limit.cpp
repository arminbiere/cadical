#include "internal.hpp"

namespace CaDiCaL {

Limit::Limit () {
  memset (this, 0, sizeof *this);
}

/*------------------------------------------------------------------------*/

double Internal::scale (double v) const {
  const double ratio = clause_variable_ratio ();
  const double factor = (ratio <= 2) ? 1.0 : log (ratio) / log (2);
  double res = factor * v;
  if (res < 1) res = 1;
  return res;
}

/*------------------------------------------------------------------------*/

bool Internal::terminating () {

  if (external->terminator && external->terminator->terminate ()) {
    LOG ("connected terminator forces termination");
    return true;
  }

  if (termination_forced) {
    LOG ("termination forced");
    return true;
  }

  if (!preprocessing &&
      !localsearching &&
      lim.conflicts >= 0 &&
      stats.conflicts >= lim.conflicts) {
    LOG ("conflict limit %" PRId64 " reached", lim.conflicts);
    return true;
  }

  if (!preprocessing &&
      !localsearching &&
      lim.decisions >= 0 &&
      stats.decisions >= lim.decisions) {
    LOG ("decision limit %" PRId64 " reached", lim.decisions);
    return true;
  }

  return false;
}

/*------------------------------------------------------------------------*/

Last::Last () {
  memset (this, 0, sizeof *this);
}

/*------------------------------------------------------------------------*/

Inc::Inc () {
  memset (this, 0, sizeof *this);
  decisions = conflicts = -1;           // unlimited
}

void Internal::limit_conflicts (int l) {
  if (l < 0 && inc.conflicts < 0) {
    LOG ("keeping unbounded conflict limit");
  } else if (l < 0) {
    LOG ("reset conflict limit to be unbounded");
    inc.conflicts = -1;
  } else {
    inc.conflicts = l;
    LOG ("new conflict limit of %d conflicts", l);
  }
}

void Internal::limit_decisions (int l) {
  if (l < 0 && inc.decisions < 0) {
    LOG ("keeping unbounded decision limit");
  } else if (l < 0) {
    LOG ("reset decision limit to be unbounded");
    inc.decisions = -1;
  } else {
    inc.decisions = stats.decisions + l;
    LOG ("new decision limit of %d decisions", l);
  }
}

void Internal::limit_preprocessing (int l) {
  if (l < 0) {
    LOG ("ignoring invalid preprocessing limit %d", l);
  } else if (!l) {
    LOG ("reset preprocessing limit to no preprocessing");
    inc.preprocessing = 0;
  } else {
    inc.preprocessing = l;
    LOG ("new preprocessing limit of %d preprocessing rounds", l);
  }
}

void Internal::limit_local_search (int l) {
  if (l < 0) {
    LOG ("ignoring invalid local search limit %d", l);
  } else if (!l) {
    LOG ("reset local search limit to no local search");
    inc.localsearch = 0;
  } else {
    inc.localsearch = l;
    LOG ("new local search limit of %d local search rounds", l);
  }
}

bool Internal::is_valid_limit (const char * name) {
  if (!strcmp (name, "conflicts")) return true;
  if (!strcmp (name, "decisions")) return true;
  if (!strcmp (name, "preprocessing")) return true;
  if (!strcmp (name, "localsearch")) return true;
  return false;
}

bool Internal::limit (const char * name, int l) {
  bool res = true;
       if (!strcmp (name, "conflicts")) limit_conflicts (l);
  else if (!strcmp (name, "decisions")) limit_decisions (l);
  else if (!strcmp (name, "preprocessing")) limit_preprocessing (l);
  else if (!strcmp (name, "localsearch")) limit_local_search (l);
  else res = false;
  return res;
}

void Internal::reset_limits () {
  LOG ("reset limits");
  limit_conflicts (-1);
  limit_decisions (-1);
  limit_preprocessing (0);
  limit_local_search (0);
}

}

