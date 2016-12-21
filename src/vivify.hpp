#ifndef _vivify_hpp_INCLUDED
#define _vivify_hpp_INCLUDED

#include <vector>

namespace CaDiCaL {

using namespace std;

struct ClauseScore {
  Clause * clause;
  long score;
  ClauseScore (Clause * c, long s) : clause (c), score (score) { }
};

struct less_clause_score {
  bool operator () (const ClauseScore & a, const ClauseScore & b) const {
    return a.score < b.score;
  }
};

typedef vector<ClauseScore> VivifySchedule;

};

#endif
