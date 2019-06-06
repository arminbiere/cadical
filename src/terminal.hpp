#ifndef _terminal_hpp_INCLUDED
#define _terminal_hpp_INCLUDED

namespace CaDiCaL {

class Terminal {

  FILE * file;          // 'stdout' or 'stderr'
  bool connected;       // Connected to terminal.
  bool use_colors;      // Use colors.
  bool reset_on_exit;   // Reset on exit.

  void escape () {
    assert (connected);
    fputs ("\033[", file);
  }

  void color (int color, bool bright) {
    if (!use_colors) return;
    assert (connected);
    escape ();
    fputc (bright ? '1' : '0', file);
    fprintf (file, ";%dm", color);
    fflush (file);
  }

  void code (const char * str) {
    if (!connected) return;
    escape ();
    fputs (str, file);
    fflush (file);
  }

public:

  Terminal (FILE * file);
  ~Terminal ();

  void disable ();              // Assume disconnected in any case.
  void force_colors ();
  void force_no_colors ();
  void force_reset_on_exit ();

  bool colors () { return use_colors; }

  operator bool () const { return connected; }

  void red (bool bright = false)     { color (31, bright); }
  void green (bool bright = false)   { color (32, bright); }
  void yellow (bool bright = false)  { color (33, bright); }
  void blue (bool bright = false)    { color (34, bright); }
  void magenta (bool bright = false) { color (35, bright); }
  void black (bool bright = false)   { color (90, bright); }
  void cyan (bool bright = false)    { color (96, bright); }

  void bold () { code ("1m"); }
  void normal () { code ("0m"); }
  void inverse () { code ("7m"); }
  void underline () { code ("4m"); }

  const char * bright_magenta_code () { return use_colors ? "\033[1;35m" : ""; }
  const char * magenta_code ()        { return use_colors ? "\033[0;35m" : ""; }
  const char * blue_code ()           { return use_colors ? "\033[0;34m" : ""; }
  const char * bright_blue_code ()    { return use_colors ? "\033[1;34m" : ""; }
  const char * yellow_code ()         { return use_colors ? "\033[0;33m" : ""; }
  const char * bright_yellow_code ()  { return use_colors ? "\033[1;33m" : ""; }
  const char * green_code ()          { return use_colors ? "\033[0;32m" : ""; }
  const char * red_code ()            { return use_colors ? "\033[0;31m" : ""; }
  const char * bright_red_code ()     { return use_colors ? "\033[1;31m" : ""; }
  const char * normal_code ()         { return use_colors ? "\033[0m"    : ""; }
  const char * bold_code ()           { return use_colors ? "\033[1m"    : ""; }

  void cursor (bool on) { code (on ? "?25h" : "?25l"); }

  void erase_until_end_of_line () { code ("K"); }

  void erase_line_if_connected_otherwise_new_line () {
    if (connected) code ("1G");
    else fputc ('\n', file), fflush (file);
  }

  void reset ();
};

extern Terminal tout;   // Terminal of 'stdout' (file descriptor '1')
extern Terminal terr;   // Terminal of 'stderr' (file descriptor '2')

}

#endif
