#ifndef _var_hpp_INCLUDED
#define _var_hpp_INCLUDED

namespace CaDiCaL {

class Clause;

// This structure captures data associated with an assigned variable.

struct Var {

  // Note that none of these members is valid unless the variable is
  // assigned.  During unassigning it we also do not need to reset it.

  int level;            // decision level

  // For assignments forced by binary clauses, watches contain already all
  // the information to track the reason for the assignment and building the
  // implication graph, namely the other 'blit' literal.  During conflict
  // analysis and clause minimization we do not really need to have access
  // to the actual clause, but simply can use a saved copy of the other
  // 'blit' literal in the watch as reason.
  // 
  // If a variable is assigned either both 'other' and 'reason' are zero,
  // and the variable is a decision or root level unit, or exactly one of
  // them is non-zero.  If 'other' is non-zero than the reason is a binary
  // clause other the actual reason clause is 'reason'.
  //
  // Splitting it here and not hiding it in a separate class makes reason
  // traversal code slightly more complicated, since it always has to
  // distinguish the two cases ('other' non-zero or 'reason' non-zero).
  // This happens in 'minimize' and 'analyze', but it is worse doing.

  int other;            // binary reason other literal
  Clause * reason;      // implication graph edge through clause

  bool decision () const { return !other && !reason; }
};

};

#endif
