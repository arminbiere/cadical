#ifndef _report_hpp_INCLUDED
#define _report_hpp_INCLUDED

namespace CaDiCaL {

struct Report {
  const char * header;
  char buffer[20];
  int pos;
  Report (const char * h, int precision, int min, double value);
  Report () { }
  void print_header (char * line);
};

};

#endif
