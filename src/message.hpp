#ifndef _message_h_INCLUDED
#define _message_h_INCLUDED

namespace CaDiCaL {

class Solver;
class File;

struct Message {
  static void print (Solver *, int verbosity, const char *, ...);
  static void die (Solver *, const char *, ...);
  static void section (Solver *, const char * title);
  static void parse_error (Solver *, File &, const char *, ...);
};

};

#define MSG(ARGS...) \
do { Message::print (solver, 0, ##ARGS); } while (0)

#define VRB(ARGS...) \
do { Message::print (solver, 1, ##ARGS); } while (0)

#define DIE(ARGS...) \
do { Message::die (solver, ##ARGS); } while (0)

#define PER(ARGS...) \
do { Message::parse_error (solver, file, ##ARGS); } while (0)

#define SECTION(ARGS...) \
do { Message::section (solver, ##ARGS); } while (0)

#endif
