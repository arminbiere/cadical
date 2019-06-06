/*
 * Copyright (c) 2009, Armin Biere, JKU, Linz, Austria.  All rights reserved.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <ctype.h>
#include <zlib.h>
#include <string.h>
#include <assert.h>

static void
die (const char * msg, ...)
{
  va_list ap;
  fputs ("*** precochk: ", stdout);
  va_start (ap, msg);
  vfprintf (stdout, msg, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
  exit (1);
}

static void
msg (const char * msg, ...)
{
  va_list ap;
  fputs ("c [precochk] ", stdout);
  va_start (ap, msg);
  vprintf (msg, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
}

int
main (int argc, char ** argv)
{
  int m, n, ch, lit, sign, c, sat, l, * stack, * top, * end;
  signed char * vals, * mark;
  gzFile dimacs, solution;
  if (argc != 3) die ("usage: precochk <dimacs> <solution>");
  if (!(solution = gzopen (argv[2], "r"))) die ("can not read '%s'", argv[2]);
  msg ("searching solution line in '%s'", argv[2]);
SKIP1:
  ch = gzgetc (solution);
  if (ch == EOF) die ("missing solution line");
  if (ch == 'c')
    {
      while ((ch = gzgetc (solution)) != '\n' && ch != EOF)
	;
      goto SKIP1;
    }
  if (ch != 's') die ("expected 'c' or 's'");
  if (gzgetc (solution) != ' ') die ("invalid solution line");
  ch = gzgetc (solution);
  if ((ch != 'S' && ch != 'U') ||
      (ch == 'S' && (gzgetc (solution) != 'A' ||
		     gzgetc (solution) != 'T' ||
		     gzgetc (solution) != 'I' ||
		     gzgetc (solution) != 'S' ||
		     gzgetc (solution) != 'F' ||
		     gzgetc (solution) != 'I' ||
		     gzgetc (solution) != 'A' ||
		     gzgetc (solution) != 'B' ||
		     gzgetc (solution) != 'L' ||
		     gzgetc (solution) != 'E')) ||
      (ch == 'U' && (gzgetc (solution) != 'N' ||
		     gzgetc (solution) != 'S' ||
		     gzgetc (solution) != 'A' ||
		     gzgetc (solution) != 'T' ||
		     gzgetc (solution) != 'I' ||
		     gzgetc (solution) != 'S' ||
		     gzgetc (solution) != 'F' ||
		     gzgetc (solution) != 'I' ||
		     gzgetc (solution) != 'A' ||
		     gzgetc (solution) != 'B' ||
		     gzgetc (solution) != 'L' ||
		     gzgetc (solution) != 'E')) ||
       gzgetc (solution) != '\n') die ("invalid solution line");
  msg ("found solution line 's %sSATISFIABLE'", ch == 'S' ? "" : "UN");
  if (ch == 'U')
    {
      msg ("unsatisfiable thus nothing to be done");
      gzclose (solution);
      exit (20);
    }
  msg ("searching dimacs header in '%s'", argv[1]);
  if (!(dimacs = gzopen (argv[1], "r"))) die ("can not read '%s'", argv[1]);
SKIP2:
  ch = gzgetc (dimacs);
  if (ch == EOF) die ("missing dimacs header");
  if (ch == 'c')
    {
      while ((ch = gzgetc (dimacs)) != '\n' && ch != EOF)
	;
      goto SKIP2;
    }
  if (ch != 'p') die ("expected 'c' or 'p'");
  if (gzgetc (dimacs) != ' ' ||
      gzgetc (dimacs) != 'c' ||
      gzgetc (dimacs) != 'n' ||
      gzgetc (dimacs) != 'f' ||
      gzgetc (dimacs) != ' ') die ("invalid header");
  ch = gzgetc (dimacs);
  if (!isdigit (ch)) die ("invalid header");
  m = ch - '0';
  while (isdigit (ch = gzgetc (dimacs)))
    m = 10  * m + (ch - '0');
  if (ch != ' ') die ("invalid header");
  ch = gzgetc (dimacs);
  if (!isdigit (ch)) die ("invalid header");
  n = ch - '0';
  while (isdigit (ch = gzgetc (dimacs)))
    n = 10 * n + (ch - '0');
  if (ch != ' ' && ch != '\n') die ("invalid header");
  msg ("found dimacs header 'p cnf %d %d'", m , n);
  vals = malloc (m + 1);
  memset (vals + 1, 0, m);
  msg ("searching for values in '%s'", argv[2]);
  c = 0;
SKIP3:
  ch = gzgetc (solution);
  if (ch == EOF) 
    { 
      if (c) die ("zero value sentinel missing");
      else die ("no values found");
    }
  if (ch == 'c')
    {
      while ((ch = gzgetc (solution)) != '\n' && ch != EOF)
	;
      goto SKIP3;
    }
  if (ch != 'v') die ("expected 'c' or 'v'");
  if (gzgetc (solution) != ' ') die ("invalid value line");
  ch = gzgetc (solution);
VAL:
  if (ch == '-')
    {
      sign = -1;
      ch = gzgetc (solution);
      if (ch == '0') die ("expected non zero digit");
    }
  else 
    sign = 1;
  if (!isdigit (ch)) die ("expected digit");
  lit = ch - '0';
  while (isdigit (ch = gzgetc (solution)))
    lit = 10 * lit + (ch - '0');
  if (ch != ' ' && ch != '\n') die ("expected space or new line");
  if (!lit) goto CHECK;
  if (lit > m) die ("value %d exceeds maximal index %d", sign * lit, m);
  if (vals[lit]) die ("multiple values for %d", lit);
  vals[lit] = sign;
  c++;
  while (ch == ' ')
    ch = gzgetc (solution);
  if (ch == '\n') goto SKIP3;
  goto VAL;
CHECK:
  assert (c <= m);
  if (c == m) msg ("found all %d values", c);
  else msg ("found %d out of %d values (%d missing)", c, m, m - c);
  mark = malloc (m + 1);
  memset (mark + 1, 0, m);
  stack = top = end = 0;
SKIP4:
  ch = gzgetc (solution);
  if (ch == 'c') 
    {
      while ((ch = gzgetc (solution)) != '\n' && ch != EOF)
	;
      goto SKIP4;
    }
  if (ch == 'v') die ("invalid new value block");
  if (ch != EOF) die ("invalid line after values");
  gzclose (solution);
  msg ("solution file closed");
  sat = c = l = 0;
LIT:
  ch = gzgetc (dimacs);
  if (ch == ' ' || ch == '\n') goto LIT;
  if (ch == 'c')
    {
      while ((ch = gzgetc (dimacs)) != '\n' && ch != EOF)
	;
      goto LIT;
    }
  if (ch == EOF)
    {
      if (l) die ("zero literal sentinel missing");
      if (c < n) die ("clauses missing");
      goto DONE;
    }
  if (ch == '-')
    {
      sign = -1;
      ch = gzgetc (dimacs);
      if (ch == '0') die ("expected non zero digit");
    }
  else
    sign = 1;
  if (!isdigit (ch)) die ("expected digit");
  if (c == n) die ("too many clauses");
  lit = ch - '0';
  while (isdigit (ch = gzgetc (dimacs)))
    lit = 10 * lit + (ch - '0');
  if (ch != ' ' && ch != '\n') die ("expected space or new line");
  if (lit) 
    {
      l++;
      if (!sat)
	{
	  if (vals[lit] == sign || mark[lit] == -sign)
	    sat = 1;
	  else 
	    {
	      if (top == end)
		{
		  int count = top - stack, size = count ? 2 * count : 1;
		  stack = realloc (stack, size * sizeof (int));
		  top = stack + count;
		  end = stack + size;
		}

	      *top++ = lit;
	      mark[lit] = sign;
	    }
	}
    }
  else
    {
      c++;
      if (!sat) die ("clause %d unsatisfied", c);
      l = sat = 0;
      while (top > stack)
	mark[*--top] = 0;
    }
  goto LIT;
DONE:
  assert (c == n);
  gzclose (dimacs);
  free (vals);
  free (stack);
  free (mark);
  msg ("checked %d clauses", c);
  msg ("satisfiable and solution correct", c);
  return 0;
}
