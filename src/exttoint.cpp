#include "exttoint.hpp"

#undef MYPRINTF
#ifdef MYPRINTFLOGGING
#define MYPRINTF(str,...) printf("c Exttoint " str "\n",  ##__VA_ARGS__)
#else
#define MYPRINTF(str,...) do {} while (0)
#endif

namespace CaDiCaL {
void ExtToInt::compress () {
  assert (!use_hash_map);
  for (size_t evar = 0; evar < vec_e2i.table.size (); ++evar) {
    int ilit = vec_e2i[evar];
    if (ilit) {
      MYPRINTF ("%zd -> %d \n", evar, ilit);
      h_e2i.insert (evar, ilit);
    }
  }
  use_hash_map = true;
}

  void ExtToInt::maybe_compress (int max_var) {
    if (use_hash_map)
      return;
    MYPRINTF ("checking if compress %d max_var\n", max_var);
    int count = 0;
    assert ((size_t)max_var < vec_e2i.table.size ());
    for (int i = 0; i <= max_var; ++i) {
      int ilit = vec_e2i[i];
      if (ilit)
        ++count;
      if (count > (max_var * 3) / 4)
        return;
    }
    if (count > (max_var * 3) / 4)
      return;
    compress ();
  }

}

#undef MYPRINTF