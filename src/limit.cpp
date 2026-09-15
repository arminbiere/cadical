#include "internal.hpp"
#include <limits>

namespace CaDiCaL {

Limit::Limit () { memset (this, 0, sizeof *this); }

/*------------------------------------------------------------------------*/

double Internal::scale (double v) const {
  const double ratio = clause_variable_ratio ();
  const double factor = (ratio <= 2) ? 1.0 : log (ratio) / log (2);
  double res = factor * v;
  if (res < 1)
    res = 1;
  return res;
}

/*------------------------------------------------------------------------*/

Last::Last () { memset (this, 0, sizeof *this); }

/*------------------------------------------------------------------------*/

Inc::Inc () {
  memset (this, 0, sizeof *this);
  ticks = decisions = conflicts = -1; // unlimited
}

void Internal::limit_terminate (int l) {
  if (l <= 0 && !lim.terminate.forced) {
    LOG ("keeping unbounded terminate limit");
  } else if (l <= 0) {
    LOG ("reset terminate limit to be unbounded");
    lim.terminate.forced = 0;
  } else {
    lim.terminate.forced = l;
    LOG ("new terminate limit of %d calls", l);
  }
}

void Internal::limit_conflicts (int64_t l) {
  if (l < 0 && inc.conflicts < 0) {
    LOG ("keeping unbounded conflict limit");
  } else if (l < 0) {
    LOG ("reset conflict limit to be unbounded");
    inc.conflicts = -1;
  } else {
    inc.conflicts = l;
    LOG ("new conflict limit of %" PRId64 " conflicts", l);
  }
}

void Internal::limit_decisions (int64_t l) {
  if (l < 0 && inc.decisions < 0) {
    LOG ("keeping unbounded decision limit");
  } else if (l < 0) {
    LOG ("reset decision limit to be unbounded");
    inc.decisions = -1;
  } else {
    inc.decisions = l;
    LOG ("new decision limit of %" PRId64 " decisions", l);
  }
}

void Internal::limit_ticks (int64_t l) {
  if (l < 0 && inc.ticks < 0) {
    LOG ("keeping unbounded ticks limit");
  } else if (l < 0) {
    LOG ("reset ticks limit to be unbounded");
    inc.ticks = -1;
  } else {
    inc.ticks = l;
    LOG ("new ticks limit of %" PRId64 " ticks", l);
  }
}

void Internal::limit_preprocessing (int64_t l) {
  if (l < 0) {
    LOG ("ignoring invalid preprocessing limit %" PRId64, l);
  } else if (!l) {
    LOG ("reset preprocessing limit to no preprocessing");
    inc.preprocessing = 0;
  } else {
    inc.preprocessing = l;
    LOG ("new preprocessing limit of %" PRId64 " preprocessing rounds", l);
  }
}

void Internal::limit_local_search (int64_t l) {
  if (l < 0) {
    LOG ("ignoring invalid local search limit %" PRId64, l);
  } else if (!l) {
    LOG ("reset local search limit to no local search");
    inc.localsearch = 0;
  } else {
    inc.localsearch = l;
    LOG ("new local search limit of %" PRId64 " local search rounds", l);
  }
}

bool Internal::is_valid_limit (const char *name) {
  if (!strcmp (name, "terminate"))
    return true;
  if (!strcmp (name, "conflicts"))
    return true;
  if (!strcmp (name, "decisions"))
    return true;
  if (!strcmp (name, "preprocessing"))
    return true;
  if (!strcmp (name, "localsearch"))
    return true;
  if (!strcmp (name, "ticks"))
    return true;
  return false;
}

bool Internal::limit (const char *name, int64_t l) {
  bool res = true;
  if (!strcmp (name, "terminate")) {
    const int64_t min = std::numeric_limits<int>::min ();
    const int64_t max = std::numeric_limits<int>::max ();
    if (l < min || l > max) {
      LOG ("terminate limit value %" PRId64
           " exceeds int numeric limits, clipping to %" PRId64,
           l, std::max (min, std::min (max, l)));
      l = std::max (min, std::min (max, l));
    }
  }
  if (!strcmp (name, "terminate"))
    limit_terminate (static_cast<int>(l));
  else if (!strcmp (name, "conflicts"))
    limit_conflicts (l);
  else if (!strcmp (name, "decisions"))
    limit_decisions (l);
  else if (!strcmp (name, "preprocessing"))
    limit_preprocessing (l);
  else if (!strcmp (name, "localsearch"))
    limit_local_search (l);
  else if (!strcmp (name, "ticks"))
    limit_ticks (l);
  else
    res = false;
  return res;
}

void Internal::reset_limits () {
  LOG ("reset limits");
  limit_terminate (0);
  limit_conflicts (-1);
  limit_decisions (-1);
  limit_preprocessing (0);
  limit_local_search (0);
  limit_ticks (-1);
}

} // namespace CaDiCaL
