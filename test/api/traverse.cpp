#include "../../src/cadical.hpp"

#ifdef NDEBUG
#undef NDEBUG
#endif

#include <cassert>
#include <cstdlib>
#include <iostream>
#include <string>

using namespace std;
using namespace CaDiCaL;

static string path (const char *suffix) {
  const char *prefix = getenv ("CADICALBUILD");
  string res = prefix ? prefix : ".";
  res += "/test-api-traverse.";
  res += suffix;
  return res;
}

struct WitnessChecker : WitnessIterator {
  bool match (int a, int b) {
    if (a == -3 && b == 1)
      return true;
    if (a == 1 && b == -3)
      return true;
    if (a == -3 && b == 2)
      return true;
    if (a == 2 && b == -3)
      return true;
    return false;
  }
  bool match (int a, int b, int c) {
    if (a == 3 && b == -1 && c == -2)
      return true;
    if (a == 3 && b == -2 && c == -1)
      return true;
    if (a == -1 && b == 3 && c == -2)
      return true;
    if (a == -2 && b == 3 && c == -1)
      return true;
    if (a == -1 && b == -2 && c == 3)
      return true;
    if (a == -2 && b == -1 && c == 3)
      return true;
    return false;
  }

public:
  bool witness (const vector<int> &c, const vector<int> &w, uint64_t) {
    for (const auto &lit : w)
      cout << lit << ' ';
    cout << "0 ";
    for (const auto &lit : c)
      cout << lit << ' ';
    cout << '0' << endl;
    if (c.size () == 1) {
      assert (c[0] == 5);
      assert (w.size () == 1);
      assert (w[0] == 5);
    } else {
      assert (w.size () == 1);
      assert (w[0] != -3);
      assert (w[0] != 3);
      assert (abs (w[0]) == 1 || abs (w[0]) == 2);
      if (c.size () == 2)
        assert (match (c[0], c[1]));
      else
        assert (c.size () == 3), assert (match (c[0], c[1], c[2]));
    }
    return true;
  }
};

struct ClauseChecker : ClauseIterator {
  bool clause (const vector<int> &c) {
    for (const auto &lit : c)
      cout << lit << ' ';
    cout << '0' << endl;
    assert (c.size () == 1);
    assert (c[0] == 4);
    return true;
  }
};

int main () {

  Solver cadical;

  // And gate 3 = 1 & 2>

  cadical.add (-3);
  cadical.add (1);
  cadical.add (0);

  cadical.add (-3);
  cadical.add (2);
  cadical.add (0);

  cadical.add (3);
  cadical.add (-1);
  cadical.add (-2);
  cadical.add (0);

  // Force 4 to true.

  cadical.add (4);
  cadical.add (1);
  cadical.add (2);
  cadical.add (0);

  cadical.add (4);
  cadical.add (-1);
  cadical.add (2);
  cadical.add (0);

  cadical.add (4);
  cadical.add (1);
  cadical.add (-2);
  cadical.add (0);

  cadical.add (4);
  cadical.add (-1);
  cadical.add (-2);
  cadical.add (0);

  // Force 5 to true too.

  cadical.add (5);
  cadical.add (1);
  cadical.add (0);

  cadical.add (5);
  cadical.add (-1);
  cadical.add (0);

  cadical.freeze (3);
  cadical.freeze (4);

  cadical.simplify (1);

  // Now we expect '5' to be part of the witness, but '3' and '4' to be part
  // the traversed clauses and check this too.  See the long comment on
  // 'frozen' versus 'non-frozen' unit traversal in 'external.cpp'.

  cadical.write_dimacs (path ("clauses").c_str (), 5);
  cadical.write_extension (path ("extensions").c_str ());

  cout << "clauses" << endl;
  ClauseChecker clause_checker;
  cadical.traverse_clauses (clause_checker);

  cout << "witnesses" << endl;
  WitnessChecker witness_checker;
  cadical.traverse_witnesses_backward (witness_checker);

  return 0;
}
