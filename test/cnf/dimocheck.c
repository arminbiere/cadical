// clang-format off
static const char * usage =
"usage: dimocheck [ <option> ... ] <dimacs> <solution>\n"
"\n"
"-h | -help         print this command line option summary\n"
"-s | --strict      strict parsing (default is relaxed parsing)\n"
"-c | --complete    require full models (default is partial model checking)\n"
"-p | --pedantic    set both strict and complete mode\n"
"-v | --verbose     print verbose information\n"
"-d | --debug       print debugging information\n"
"-q | --quiet       no messages except the status line, warnings and errors\n"
"     --silent      really no message at all (exit code determines success)\n"
"     --banner      only print banner\n"
"     --version     only print version\n"
"\n"
"The first file '<dimacs>' is supposed to be a formula in DIMACS format and\n"
"the second '<solution>' file should have the SAT competition output format,\n"
"with comment lines 'c', the status line 's', i.e., 's SATISFIABLE' and\n"
"potentially several 'v' value lines.\n"
"\n"
"If the files are compressed, i.e., their file name has a '.gz', '.xz',\n"
"'.bz2' file name suffix, then the tools tries to open them through a pipe\n"
"and relies on the existence of external tools 'gzip', 'xz', or 'bzip2' to\n"
"perform the actual decompression.\n"
"\n"
"If checking succeeds the program returns with exit code '0' and prints the\n"
"line 's MODEL_SATISFIES_FORMULA' on '<stdout>'.  Errors are reported on\n"
"'<stderr>' and lead to a non-zero exit code.  Only 's SATISFIABLE' is\n"
"supported as status line and other status lines, e.g., 's UNSATISFIABLE' or\n"
"'s UNKNOWN', are considered an error (even in relaxed mode).\n"
"\n"
"By default the parsing and checking is more relaxed.  For instance more\n"
"spaces and comments are allowed and also the 'p cnf ...' header line can\n"
"have arbitrary values.  We further only require by default a partial model,\n"
"i.e., not all variables need to occur in 'v' lines, as long they still\n"
"satisfy each clause (a literal without value is treated as false in each\n"
"clause).  Strict and complete parsing and checking can be enforced with\n"
"'--strict', '--complete', or '--pedantic'.\n"
;
// clang-format on

#include "config.h"

#include <assert.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <sys/resource.h>

#define PREFIX "[dimocheck] "

static int verbosity;
static bool complete;
static bool strict;

static const char *strict_option;
static const char *complete_option;

struct clause {
  size_t lineno;
  size_t column;
  size_t size;
  int literals[];
};

static const char *dimacs_path;
static const char *model_path;

static FILE *file;
static int close_file;
static size_t lineno;
static size_t column;
static size_t charno;
static const char *path;
static int last_char[2];

static int maximum_dimacs_variable;
static int maximum_model_variable;
static size_t parsed_clauses;

static struct {
  int *begin, *end, *allocated;
} literals;

static struct {
  struct clause **begin, **end, **allocated;
} clauses;

static struct {
  int *begin;
  size_t size, capacity;
} values;

static void msg(const char *, ...) __attribute__((format(printf, 1, 2)));
static void vrb(const char *, ...) __attribute__((format(printf, 1, 2)));

static void die(const char *, ...) __attribute__((format(printf, 1, 2)));
static void fatal(const char *, ...) __attribute__((format(printf, 1, 2)));

static void err(size_t, const char *, ...)
    __attribute__((format(printf, 2, 3)));

static void srr(size_t, const char *, ...)
    __attribute__((format(printf, 2, 3)));

static void wrr(size_t, const char *, ...)
    __attribute__((format(printf, 2, 3)));

static void wrn(const char *, ...) __attribute__((format(printf, 1, 2)));

static void msg(const char *fmt, ...) {
  if (verbosity < 0)
    return;
  fputs(PREFIX, stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

static void vrb(const char *fmt, ...) {
  if (verbosity < 1)
    return;
  fputs(PREFIX, stdout);
  va_list ap;
  va_start(ap, fmt);
  vprintf(fmt, ap);
  va_end(ap);
  fputc('\n', stdout);
  fflush(stdout);
}

static void die(const char *fmt, ...) {
  if (verbosity != INT_MIN) {
    fputs("dimocheck: error: ", stderr);
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
  }
  exit(1);
}

static void fatal(const char *fmt, ...) {
  if (verbosity != INT_MIN) {
    fputs("dimocheck: fatal error: ", stderr);
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
  }
  abort();
  exit(1); // Unreachable but kept for safety.
}

static void err(size_t token, const char *fmt, ...) {
  assert(last_char[0] != '\n' || lineno > 1);
  if (verbosity != INT_MIN) {
    fprintf(stderr, "%s:%zu:%zu: parse error: ", path,
            lineno - (last_char[0] == '\n'), token);
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
  }
  exit(1);
}

static void srr(size_t token, const char *fmt, ...) {
  assert(last_char[0] != '\n' || lineno > 1);
  if (verbosity != INT_MIN) {
    fprintf(stderr, "%s:%zu:%zu: strict parsing error: ", path,
            lineno - (last_char[0] == '\n'), token);
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
  }
  exit(1);
}

static void wrr(size_t token, const char *fmt, ...) {
  assert(last_char[0] != '\n' || lineno > 1);
  if (verbosity < 0)
    return;
  fprintf(stderr, "%s:%zu:%zu: warning: ", path,
          lineno - (last_char[0] == '\n'), token);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  fflush(stderr);
}

static void wrn(const char *fmt, ...) {
  if (verbosity < 0)
    return;
  fprintf(stderr, "%s: warning: ", path);
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
  fputc('\n', stderr);
  fflush(stderr);
}

static bool full_literals(void) { return literals.end == literals.allocated; }

static size_t size_literals(void) { return literals.end - literals.begin; }

static size_t capacity_literals(void) {
  return literals.allocated - literals.begin;
}

static void enlarge_literals(void) {
  const size_t old_capacity = capacity_literals();
  const size_t new_capacity = old_capacity ? 2 * old_capacity : 1;
  literals.begin =
      realloc(literals.begin, new_capacity * sizeof *literals.begin);
  if (!literals.begin)
    fatal("out-of-memory reallocating stack of literals");
  literals.end = literals.begin + old_capacity;
  literals.allocated = literals.begin + new_capacity;
  vrb("enlarged literal stack to %zu", new_capacity);
}

static void push_literal(int lit) {
  assert(lit);
  if (full_literals())
    enlarge_literals();
  *literals.end++ = lit;
}

static void clear_literals(void) { literals.end = literals.begin; }

static bool full_clauses(void) { return clauses.end == clauses.allocated; }

static size_t capacity_clauses(void) {
  return clauses.allocated - clauses.begin;
}

static void enlarge_clauses(void) {
  const size_t old_capacity = capacity_clauses();
  const size_t new_capacity = old_capacity ? 2 * old_capacity : 1;
  clauses.begin = realloc(clauses.begin, new_capacity * sizeof *clauses.begin);
  if (!clauses.begin)
    fatal("out-of-memory reallocating stack of clauses");
  clauses.end = clauses.begin + old_capacity;
  clauses.allocated = clauses.begin + new_capacity;
  vrb("enlarged clauses stack to %zu", new_capacity);
}

static size_t bytes_clause(size_t size) {
  return sizeof(struct clause) + size * sizeof(int);
}

static void push_clause(size_t lineno, size_t column) {
  size_t size = size_literals();
  size_t bytes = bytes_clause(size);
  struct clause *clause = malloc(bytes);
  if (!clause)
    fatal("out-of-memory allocating clause");
  clause->size = size;
  clause->lineno = lineno;
  clause->column = column;
  size_t bytes_literals = size * sizeof(int);
  memcpy(clause->literals, literals.begin, bytes_literals);
  if (full_clauses())
    enlarge_clauses();
  *clauses.end++ = clause;
  if (verbosity == INT_MAX) {
    printf(PREFIX "new size %zu clause[%zu]", size, parsed_clauses);
    const int *p = clause->literals, *end = p + size;
    while (p != end)
      printf(" %d", *p++);
    fputc('\n', stdout);
    fflush(stdout);
  }
}

static void fit_values(size_t idx) {
  assert(idx <= (size_t)INT_MAX);
  const size_t old_capacity = values.capacity;
  if (idx >= old_capacity) {
    size_t new_capacity = old_capacity ? 2 * old_capacity : 1;
    while (idx >= new_capacity)
      new_capacity *= 2;
    values.begin = realloc(values.begin, new_capacity * sizeof *values.begin);
    if (!values.begin)
      fatal("out-of-memory reallocating value array");
    values.capacity = new_capacity;
  }
  while (idx >= values.size) {
    assert(values.size < values.capacity);
    values.begin[values.size++] = 0;
  }
}

static bool has_suffix(const char *p, const char *q) {
  size_t k = strlen(p), l = strlen(q);
  return k >= l && !strcmp(p + k - l, q);
}

static FILE *read_zipped(const char *zipper, const char *p) {
  size_t len = strlen(p) + 32;
  char *cmd = malloc(len);
  if (!cmd)
    fatal("out-of-memory allocating unzipping command");
  snprintf(cmd, len, "%s -c -d %s", zipper, p);
  FILE *file = popen(cmd, "r");
  free(cmd);
  return file;
}

static void init_parsing(const char *p) {
  close_file = 2;
  if (has_suffix(p, ".bz2"))
    file = read_zipped("bunzip2", p);
  else if (has_suffix(p, ".gz"))
    file = read_zipped("gzip", p);
  else if (has_suffix(p, ".xz"))
    file = read_zipped("xz", p);
  else {
    file = fopen(path = p, "r");
    close_file = 1;
  }
  if (!file)
    die("can not open and read '%s'", path);
  last_char[0] = last_char[1] = EOF;
  lineno = 1;
  column = 0;
  charno = 0;
}

static void reset_parsing(void) {
  vrb("closing '%s'", path);
  if (close_file == 1)
    fclose(file);
  if (close_file == 2)
    pclose(file);
}

static int next_char(void) {
  int res = getc(file);
  if (res == '\n')
    lineno++;
  if (res != EOF) {
    if (last_char[0] == '\n')
      column = 1;
    else
      column++;
    charno++;
  }
  last_char[1] = last_char[0];
  last_char[0] = res;
  return res;
}

static bool is_space(int ch) {
  return ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n';
}

static bool is_digit(int ch) { return '0' <= ch && ch <= '9'; }

static const char *space_name(int ch) {
  assert(is_space(ch));
  if (ch == ' ')
    return "space ' '";
  if (ch == '\t')
    return "tab-character '\\t'";
  if (ch == '\r')
    return "carriage-return '\\r'";
  assert(ch == '\n');
  return "new-line '\\n'";
}

static void parse_dimacs(void) {
  init_parsing(dimacs_path);
  msg("parsing DIMACS '%s'", path);
  if (strict) {
    assert(strict_option);
    msg("parsing in strict mode (due to '%s')", strict_option);
  } else
    msg("parsing in relaxed mode (without '--strict' nor '--pedantic')");
  for (;;) {
    int ch = next_char();
    if (ch == EOF) {
      if (charno)
        err(column, "end-of-file before header (truncated file)");
      else
        err(column, "end-of-file before header (empty file)");
    } else if (is_space(ch)) {
      if (strict)
        srr(column, "expected 'c' or 'p' at start of line");
    } else if (ch == 'c') {
      while ((ch = next_char()) != '\n')
        if (ch == EOF)
          err(column, "end-of-file in header comment");
      continue;
    } else if (ch == 'p')
      break;
    else
      err(column, "unexpected character (expected 'p' or 'c')");
  }
  int ch = next_char();
  if (strict) {
    if (ch != ' ')
      srr(column, "expected %s after 'p'", space_name(' '));
    ch = next_char();
  } else {
    if (ch != ' ' && ch != '\t')
      err(column, "expected %s or %s after 'p'", space_name(' '),
          space_name('\t'));
    do
      ch = next_char();
    while (ch == ' ' || ch == '\t');
  }
  if (ch != 'c')
    err(column, "expected 'c'");
  ch = next_char();
  if (ch != 'n')
    err(column, "expected 'n' after 'c'");
  ch = next_char();
  if (ch != 'f')
    err(column, "expected 'f' after 'cn'");
  ch = next_char();
  if (strict) {
    if (ch != ' ')
      srr(column, "expected %s after 'p cnf'", space_name(' '));
    ch = next_char();
  } else {
    if (ch != ' ' && ch != '\t')
      err(column, "expected %s or %s after 'cnf'", space_name(' '),
          space_name('\t'));
    do
      ch = next_char();
    while (ch == ' ' || ch == '\t');
  }
  size_t specified_variables;
  {
    if (!is_digit(ch))
      err(column, "expected digit after 'p cnf '");
    const size_t maximum_variables_limit = INT_MAX;
    specified_variables = ch - '0';
    while (is_digit(ch = next_char())) {
      if (strict && !specified_variables)
        srr(column - 1, "leading '0' digit in number of variables");
      if (maximum_variables_limit / 10 < specified_variables)
        err(column, "maximum variable limit exceeded");
      specified_variables *= 10;
      unsigned digit = ch - '0';
      if (maximum_variables_limit - digit < specified_variables)
        err(column, "maximum variable limit exceeded");
      specified_variables += digit;
    }
  }
  if (strict) {
    if (ch != ' ')
      srr(column, "expected %s after 'p cnf %zu'", space_name(' '),
          specified_variables);
    ch = next_char();
  } else {
    if (ch != ' ' && ch != '\t')
      err(column, "expected %s or %s after 'cnf %zu'", space_name(' '),
          space_name('\t'), specified_variables);
    do
      ch = next_char();
    while (ch == ' ' || ch == '\t');
  }
  size_t specified_clauses;
  {
    if (!is_digit(ch))
      err(column, "expected digit after 'p cnf %zu '", specified_variables);
    const size_t maximum_clauses_limit = ~(size_t)0;
    specified_clauses = ch - '0';
    while (is_digit(ch = next_char())) {
      if (strict && !specified_clauses)
        srr(column - 1, "leading '0' digit in number of clauses");
      if (maximum_clauses_limit / 10 < specified_clauses)
        err(column, "maximum clauses limit exceeded");
      specified_clauses *= 10;
      unsigned digit = ch - '0';
      if (maximum_clauses_limit - digit < specified_clauses)
        err(column, "maximum clauses limit exceeded");
      specified_clauses += digit;
    }
    if (ch == EOF) {
      if (strict)
        srr(column, "end-of-file after 'p cnf %zu %zu'", specified_variables,
            specified_clauses);
      else if (specified_clauses)
        err(column, "end-of-file after 'p cnf %zu %zu'", specified_variables,
            specified_clauses);
    }
    if (strict) {
      if (ch == '\r') {
        ch = next_char();
        if (ch != '\n')
          srr(column, "expected %s after %s after 'p cnf %zu %zu'",
              space_name('\n'), space_name('\r'), specified_variables,
              specified_clauses);
      } else if (ch != '\n')
        srr(column, "expected %s after 'p cnf %zu %zu'", space_name(' '),
            specified_variables, specified_clauses);
      ch = next_char();
    } else {
      if (ch == 'c') {
        while ((ch = next_char()) != '\n' && ch != EOF)
          ;
      } else {
        if (!is_space(ch) && ch != EOF)
          err(column, "expected %s or %s after 'p cnf %zu %zu'",
              space_name(' '), space_name('\n'), specified_variables,
              specified_clauses);
        while (is_space(ch) && ch != '\n')
          ch = next_char();
      }
      if (ch == EOF && specified_clauses)
        err(column, "end-of-file after 'p cnf %zu %zu'", specified_variables,
            specified_clauses);
    }
  }
  msg("parsed header 'p cnf %zu %zu'", specified_variables, specified_clauses);
  {
    size_t variables_specified_exceeded = 0;
    size_t clause_lineno = lineno;
    size_t clause_column = column;
    int last_lit = 0;

    for (;;) {

      size_t token = column;

      if (ch == EOF) {
      PARSED_END_OF_FILE:
        if (last_lit)
          err(column, "terminating zero '0' missing in last clause");

        if (parsed_clauses < specified_clauses) {
          const size_t missing_clauses = specified_clauses - parsed_clauses;
          if (strict) {
            if (missing_clauses == 1)
              srr(column, "one clause missing (parsed %zu but %zu specified)",
                  parsed_clauses, specified_clauses);
            else
              srr(column, "%zu clauses missing (parsed %zu but %zu specified)",
                  missing_clauses, parsed_clauses, specified_clauses);
          } else {
            if (missing_clauses == 1)
              wrn("one clause missing (parsed %zu but %zu specified)",
                  parsed_clauses, specified_clauses);
            else
              wrn("%zu clauses missing (parsed %zu but %zu specified)",
                  missing_clauses, parsed_clauses, specified_clauses);
          }
        } else if (parsed_clauses > specified_clauses) {
          assert(!strict);
          const size_t more_clauses_than_specified =
              parsed_clauses - specified_clauses;
          if (more_clauses_than_specified == 1)
            wrn("one clause more than specified "
                "(parsed %zu but %zu specified)",
                parsed_clauses, specified_clauses);
          else
            wrn("%zu more clauses than specified "
                "(parsed %zu but %zu specified)",
                more_clauses_than_specified, parsed_clauses, specified_clauses);
        }

        if (variables_specified_exceeded)
          wrn("parsed %zu literals exceeding specified maximum variable '%zu' "
              "(maximum parsed variable index '%d')",
              variables_specified_exceeded, specified_variables,
              maximum_dimacs_variable);

        break;
      }

      if (is_space(ch)) {
        if (strict)
          srr(column, "unexpected %s (expected literal)", space_name(ch));
        ch = next_char();
        continue;
      }

      if (ch == 'c') {
        if (strict)
          srr(column, "unexpected comment 'c' (after 'p cnf' header)");
        while ((ch = next_char()) != '\n')
          if (ch == EOF) {
            if (strict)
              err(column, "end-of-file in comment");
            else {
              wrr(column, "end-of-file in comment");
              goto PARSED_END_OF_FILE;
            }
          }
        ch = next_char();
        continue;
      }

      if (!last_lit) {
        clause_lineno = lineno;
        clause_column = column;
      }

      int sign = 1;
      if (ch == '-') {
        ch = next_char();
        if (strict && ch == '0')
          srr(column, "invalid '0' after '-'");
        if (!is_digit(ch))
          err(column, "expected digit after '-'");
        sign = -1;
      } else if (!is_digit(ch))
        err(column, "expected integer literal (digit or sign)");

      const size_t maximum_variable_index = INT_MAX;
      size_t idx = ch - '0';
      while (is_digit(ch = next_char())) {
        if (strict && !idx)
          srr(column - 1, "leading '0' digit in literal");
        if (maximum_variable_index / 10 < idx)
          err(column, "literal exceeds maximum variable limit");
        idx *= 10;
        const unsigned digit = ch - '0';
        if (maximum_variable_index - digit < idx)
          err(column, "literal exceeds maximum variable limit");
        idx += digit;
      }

      const int lit = sign * (int)idx;
      assert(abs(lit) <= maximum_variable_index);

      if (!is_space(ch) && ch != 'c')
        err(column, "unexpected character after literal '%d'", lit);

      if (strict && specified_clauses == parsed_clauses)
        srr(token,
            "too many clauses "
            "(start of clause %zu but only %zu specified)",
            parsed_clauses + 1, specified_clauses);

      if (idx > specified_variables) {
        if (strict)
          srr(token, "literal '%d' exceeds specified maximum variable '%zu'",
              lit, specified_variables);
        else {
          if (!variables_specified_exceeded)
            wrr(token, "literal '%d' exceeds specified maximum variable '%zu'",
                lit, specified_variables);
          else if (variables_specified_exceeded == 1)
            wrr(token,
                "another literal '%d' exceeds specified maximum variable '%zu' "
                "(will stop warning about additional ones)",
                lit, specified_variables);
          variables_specified_exceeded++;
        }
      }

      if (strict && idx && ch != ' ')
        srr(column, "expected %s after literal '%d'", space_name(' '), lit);

      if (strict && !idx) {
        if (ch == '\r') {
          ch = next_char();
          if (ch != '\n')
            srr(column,
                "expected %s after carriage-return after terminating zero '0'",
                space_name('\n'));
        } else if (ch != '\n')
          srr(column, "expected %s after terminating zero '0'",
              space_name('\n'));
      }

      if (strict && sign < 0 && !lit)
        srr(token, "negative zero literal '-0'");

      if (lit) {
        push_literal(lit);
        if (idx > maximum_dimacs_variable)
          maximum_dimacs_variable = idx;
      } else {
        parsed_clauses++;
        push_clause(clause_lineno, clause_column);
        clear_literals();
      }
      last_lit = lit;

      if (strict) {
        assert((lit && ch == ' ') || (!lit && ch == '\n'));
        ch = next_char();
      }
    }
  }
  reset_parsing();
  msg("parsed %zu clauses with maximum variable index '%d'", parsed_clauses,
      maximum_dimacs_variable);
}

static double average(double a, double b) { return b ? a / b : 0; }
static double percent(double a, double b) { return average(100 * a, b); }

static void parse_model(void) {

  init_parsing(model_path);
  msg("parsing model '%s'", path);
  if (strict) {
    assert(strict_option);
    msg("parsing in strict mode (due to '%s')", strict_option);
  } else
    msg("parsing in relaxed mode (without '--strict' nor '--pedantic')");

  size_t parsed_values = 0, positive_values = 0, negative_values = 0;

  bool reported_missing_status_line = false;
  bool reported_found_status_line = false;
  size_t dimacs_variable_exceeded = 0;
  size_t first_vline_section = 0;
  size_t first_status_line = 0;
  size_t value_sections = 0;
  size_t status_lines = 0;

  int ch = next_char();
  for (;;) {

    if (ch == EOF)
      break;

    if (is_space(ch)) {
      if (strict)
        srr(column, "unexpected %s (expected 'c' or 's')", space_name(ch));
      ch = next_char();
      continue;
    }

    size_t token = column;
    if (ch == 'c') {
      while ((ch = next_char()) != '\n')
        if (ch == EOF)
          err(column, "end-of-file in comment");
      ch = next_char();

      continue; // With outer 'for' loop.
    }

    if (ch == 's') {
      const size_t start_of_status_line = lineno;
      ch = next_char();
      if (strict) {
        if (ch != ' ')
          srr(column, "expected %s after 's'", space_name(' '));
        ch = next_char();
      } else {
        if (ch != ' ' && ch != '\t')
          srr(column, "expected %s or %s after 's'", space_name(' '),
              space_name('\t'));
        do
          ch = next_char();
        while (ch == ' ' || ch == '\t');
      }
      for (const char *p = "SATISFIABLE"; *p; p++)
        if (ch != *p)
          err(token, "invalid status line (expected 's SATISFIABLE')");
        else
          ch = next_char();
      if (strict) {
        if (ch == '\r') {
          ch = next_char();
          if (ch != '\n')
            srr(column, "expected %s after %s after 's SATISFIABLE'",
                space_name('\n'), space_name('\r'));
        }
        if (ch != '\n')
          srr(column, "expected %s after 's SATISFIABLE'", space_name('\n'));
        if (strict && status_lines)
          srr(token, "second 's SATISFIABLE' line (first at line %zu)",
              first_status_line);
      } else {
        while (ch != EOF && ch != '\n' && is_space(ch))
          ch = next_char();
      }
      if (!reported_found_status_line) {
        msg("found 's SATISFIABLE' status line");
        reported_found_status_line = true;
      }
      if (!status_lines++)
        first_status_line = start_of_status_line;

      if (ch == '\n')
        ch = next_char();
      continue; // With outer 'for' loop.
    }

    if (ch == 'v') {

      if (!status_lines) {
        if (strict)
          srr(column, "'v' line without 's SATISFIABLE' status line");
        else if (!reported_missing_status_line) {
          wrr(column, "'v' line without 's SATISFIABLE' status line");
          reported_missing_status_line = true;
        }
      }

      if (value_sections++) {
        if (strict)
          srr(column, "second 'v' line (first at line %zu)",
              first_vline_section);
        else if (value_sections == 2)
          wrr(column, "second 'v' line section (first at line %zu)",
              first_vline_section);
        else if (value_sections == 3)
          wrr(column, "third 'v' line section (will stop warning about more)");
      }

      if (!first_vline_section)
        first_vline_section = lineno;

      for (;;) { // Ranges over all 'v' lines of one section.

        ch = next_char();
        if (strict) {
          if (ch != ' ')
            srr(column, "expected %s after 'v'", space_name(' '));
          ch = next_char();
        } else {
        PARSE_SPACE_AFTER_V:
          if (ch != ' ' && ch != '\t')
            err(column, "expected %s or %s after 'v'", space_name(' '),
                space_name('\t'));
          while (ch == ' ' || ch == '\t')
            ch = next_char();
        }

        for (;;) { // Ranges over values in one 'v' line.

          if (ch == EOF)
            err(column, "end-of-file in 'v' line");

          if (!strict && ch == '\n') {
          CONTINUE_IN_VLINE_AFTER_NEW_LINE:
            ch = next_char();
            if (ch != 'v')
              err(column, "expected 'v' as first character");
            ch = next_char();
            goto PARSE_SPACE_AFTER_V;
          }

          token = column;

          int sign = 1;
          if (ch == '-') {
            ch = next_char();
            if (strict && ch == '0')
              srr(column, "invalid '0' after '-'");
            if (!is_digit(ch))
              err(column, "expected digit after '-'");
            sign = -1;
          } else if (!is_digit(ch))
            err(column, "expected integer literal (digit or sign)");

          const size_t maximum_variable_index = INT_MAX;
          size_t idx = ch - '0';
          while (is_digit(ch = next_char())) {
            if (strict && !idx)
              srr(column - 1, "leading '0' digit in literal");
            if (maximum_variable_index / 10 < idx)
              err(column, "literal exceeds maximum variable limit");
            idx *= 10;
            const unsigned digit = ch - '0';
            if (maximum_variable_index - digit < idx)
              err(column, "literal exceeds maximum variable limit");
            idx += digit;
          }

          const int lit = sign * (int)idx;
          assert(abs(lit) <= maximum_variable_index);

          if (idx > maximum_dimacs_variable) {
            if (strict)
              srr(token, "literal '%d' exceeds maximum DIMACS variable '%d'",
                  lit, maximum_dimacs_variable);
            else if (!dimacs_variable_exceeded)
              wrr(token, "literal '%d' exceeds maximum DIMACS variable '%d'",
                  lit, maximum_dimacs_variable);
            else if (dimacs_variable_exceeded == 1)
              wrr(token,
                  "another literal '%d' exceeds maximum DIMACS variable '%d' "
                  "(will stop warning about additional ones)",
                  lit, maximum_dimacs_variable);
            dimacs_variable_exceeded++;
          }

          if (verbosity == INT_MAX) {
            if (lit)
              printf(PREFIX "parsed value literal '%d'\n", lit);
            else
              printf(PREFIX "parsed terminating zero '0'\n");
            fflush(stdout);
          }

          if (idx) {
            parsed_values++;
            if (idx > maximum_model_variable)
              maximum_model_variable = idx;
          }

          if (idx >= values.size)
            fit_values(idx);

          assert(idx <= (size_t)INT_MAX);
          const int old_value = values.begin[idx];
          const int new_value = lit;

          if (old_value && old_value != new_value)
            err(token, "old value '%d' overwritten by new value '%d'",
                old_value, new_value);

          if (strict && old_value) {
            assert(old_value == new_value);
            srr(token, "value '%d' set twice", new_value);
          }

          if (old_value != new_value) {
            if (new_value < 0)
              negative_values++;
            else
              positive_values++;
          }
          values.begin[idx] = new_value;

          if (lit) {

            if (strict) {
              if (ch != ' ')
                srr(column, "expected %s after '%d'", space_name(' '), lit);

              ch = next_char();

            } else {
              if (!is_space(ch))
                err(column, "expected white-space after '%d'", lit);
              while (ch != '\n' && is_space(ch))
                ch = next_char();
              if (ch == '\n')
                goto CONTINUE_IN_VLINE_AFTER_NEW_LINE;
            }

          } else {

            if (strict) {
              if (ch == '\r') {
                ch = next_char();
                if (ch != '\n')
                  srr(column, "expected %s after %s after '0'",
                      space_name('\n'), space_name('\r'));
              } else if (ch != '\n')
                srr(column, "expected %s after '0'", space_name('\n'));

            } else {
              while (ch != '\n' && is_space(ch))
                ch = next_char();
              if (ch == 'c') {
                while ((ch = next_char()) != '\n')
                  if (ch == EOF) {
                    wrr(column, "end-of-file in comment after '0'");
                    break;
                  }
              } else if (ch != EOF && ch != '\n')
                err(column, "expected %s after '0'", space_name('\n'));
            }

            if (ch != EOF) {
              assert(ch == '\n');
              ch = next_char();
            }
            goto CONTINUE_WITH_OUTER_LOOP;
          }

        } // End of 'for' loop over all all values in one 'v' line.

      } // End of 'for' loop over all 'v' lines of one section.

      continue; // With outer loop (new 'c', 's, or 'v' lines).
    }

    err(column, "expected 'c', 's' or 'v' as first character");

  CONTINUE_WITH_OUTER_LOOP:;
  } // End of outer 'for' loop over 'c', 's' and 'v' parts.

  reset_parsing();
  size_t total_set = positive_values + negative_values;
  msg("parsed %zu and set %zu values of variables with maximum index '%d'",
      parsed_values, total_set, maximum_model_variable);
  msg("set %zu positive %.2f%% and %zu negative values %.2f%%", positive_values,
      percent(positive_values, total_set), negative_values,
      percent(negative_values, total_set));
}

static void check_model(void) {
  msg("checking model to satisfy DIMACS formula");
  if (complete) {
    msg("checking completeness of model (due to '%s')", complete_option);
    for (size_t idx = 1; idx <= (size_t)maximum_dimacs_variable; idx++)
      if (idx >= values.size || !values.begin[idx])
        die("complete checking mode: "
            "value for DIMACS variable '%zu' missing",
            idx);
    msg("model complete (all DIMACS variables are assigned)");
  } else
    msg("partial model checking (without '--complete' nor '--pedantic')");
  for (struct clause **p = clauses.begin; p != clauses.end; p++) {
    const struct clause *c = *p;
    const int *q = c->literals, *end_literals = q + c->size;
    bool satisfied = false;
    while (!satisfied && q != end_literals) {
      const int lit = *q++;
      assert(lit != INT_MIN);
      const size_t idx = abs(lit);
      if (idx >= values.size)
        continue;
      int value = values.begin[idx];
      if (value == lit)
        satisfied = true;
    }
    if (satisfied)
      continue;
    fprintf(stderr, "%s:%zu:%zu: error: clause[%zu] unsatisfied:\n",
            dimacs_path, c->lineno, c->column, p - clauses.begin + 1);
    for (q = c->literals; q != end_literals; q++)
      fprintf(stderr, "%d ", *q);
    fputs("0\n", stderr);
    fflush(stderr);
    exit(1);
  }
  msg("checked all %zu clauses to be satisfied by model", parsed_clauses);
}

static void can_not_combine(const char *a, const char *b) {
  if (a && b)
    die("can not combine '%s' and '%s' (try '-h')", a, b);
}

size_t maximum_resident_set_size(void) {
  size_t res = 0;
  struct rusage u;
  if (!getrusage(RUSAGE_SELF, &u)) {
    res = (size_t)u.ru_maxrss;
#ifndef __APPLE__
    res <<= 10;
#endif
  }
  return res;
}

static double process_time(void) {
  double res = 0;
  struct rusage u;
  if (!getrusage(RUSAGE_SELF, &u)) {
    res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
    res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  }
  return res;
}

int main(int argc, char **argv) {
  const char *pedantic_option = 0;
  const char *verbose_option = 0;
  const char *debug_option = 0;
  const char *quiet_option = 0;
  const char *silent_option = 0;
  for (int i = 1; i != argc; i++) {
    const char *arg = argv[i];
    if (!strcmp(arg, "-h") || !strcmp(arg, "--help")) {
      fputs(usage, stdout);
      return 0;
    } else if (!strcmp(arg, "-s") || !strcmp(arg, "--strict")) {
      strict_option = arg;
      can_not_combine(pedantic_option, strict_option);
      strict = true;
    } else if (!strcmp(arg, "-c") || !strcmp(arg, "--complete")) {
      complete_option = arg;
      can_not_combine(pedantic_option, complete_option);
      complete = true;
    } else if (!strcmp(arg, "-p") || !strcmp(arg, "--pedantic")) {
      pedantic_option = arg;
      can_not_combine(strict_option, pedantic_option);
      can_not_combine(complete_option, pedantic_option);
      strict_option = complete_option = pedantic_option;
      strict = complete = true;
    } else if (!strcmp(arg, "-v") || !strcmp(arg, "--verbose")) {
      verbose_option = arg;
      can_not_combine(debug_option, verbose_option);
      can_not_combine(quiet_option, verbose_option);
      can_not_combine(silent_option, verbose_option);
      verbosity = 1;
    } else if (!strcmp(arg, "-d") || !strcmp(arg, "--debug")) {
      debug_option = arg;
      can_not_combine(verbose_option, debug_option);
      can_not_combine(quiet_option, debug_option);
      can_not_combine(silent_option, debug_option);
      verbosity = INT_MAX;
    } else if (!strcmp(arg, "-q") || !strcmp(arg, "--quiet")) {
      quiet_option = arg;
      can_not_combine(debug_option, quiet_option);
      can_not_combine(verbose_option, quiet_option);
      can_not_combine(silent_option, quiet_option);
      verbosity = -1;
    } else if (!strcmp(arg, "--silent")) {
      silent_option = arg;
      can_not_combine(debug_option, silent_option);
      can_not_combine(verbose_option, silent_option);
      can_not_combine(quiet_option, silent_option);
      verbosity = INT_MIN;
    } else if (arg[0] == '-')
      die("invalid option '%s' (try '-h')", arg);
    else if (!dimacs_path)
      dimacs_path = arg;
    else if (!model_path)
      model_path = arg;
    else
      die("too many files '%s', '%s' and '%s'", dimacs_path, model_path, arg);
  }
  if (!dimacs_path)
    die("DIMACS file missing (try '-h')");
  if (!model_path)
    die("model file missing (try '-h')");
  if (verbosity >= 0) {
    msg("DiMoCheck DIMACS Model Checker");
    msg("Copyright (c) 2025, Armin Biere, University of Freiburg");
    msg("Version %s", VERSION);
    msg("Compiled with '%s'", COMPILE);
  }
  parse_dimacs();
  parse_model();
  check_model();
  free(literals.begin);
  for (struct clause **p = clauses.begin; p != clauses.end; p++)
    free(*p);
  free(clauses.begin);
  free(values.begin);
  if (verbosity != INT_MIN) {
    fputs("s MODEL_SATISFIES_FORMULA\n", stdout);
    fflush(stdout);
  }
  if (verbosity >= 0) {
    size_t bytes = maximum_resident_set_size();
    if (bytes >= 1u << 30)
      msg("maximum resident-set size %.2f GB (%zu bytes)",
          bytes / (double)(1u << 30), bytes);
    else
      msg("maximum resident-set size %.2f MB (%zu bytes)",
          bytes / (double)(1 << 20), bytes);
    msg("total process-time %.2f seconds", process_time());
  }
  return 0;
}
