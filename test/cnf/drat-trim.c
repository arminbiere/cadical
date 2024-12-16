/************************************************************************************[drat-trim.c]
Copyright (c) 2014 Marijn Heule and Nathan Wetzler, The University of Texas
at Austin. Copyright (c) 2015-2017 Marijn Heule, The University of Texas at
Austin. Last edit, December 21, 2017

# Minor fixes to have proper exit code for unit testing (Armin Biere)
# Removed carriage return '\r' printing too (Armin Biere)

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
**************************************************************************************************/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/time.h>

#define TIMEOUT 20000
#define BIGINIT 1000000
#define INIT 4
#define END 0
#define UNSAT 0
#define SAT 1
#define ID -1
#define PIVOT -2
#define MAXDEP -3
#define EXTRA 4    // ID + PIVOT + MAXDEP + terminating 0
#define INFOBITS 2 // could be 1 for SAT, must be 2 for QBF
#define DBIT 1
#define ASSUMED 2
#define MARK 3
#define ERROR -1
#define ACTIVE 1

#define FORWARD_SAT 10
#define FORWARD_UNSAT 20
#define BACKWARD_UNSAT 30
#define SUCCESS 40
#define FAILED 50
#define FIXPOINT 60
#define NOWARNING 70
#define HARDWARNING 80

#define COMPRESS

struct solver {
  FILE *inputFile, *proofFile, *lratFile, *traceFile, *activeFile;
  int *DB, nVars, timeout, mask, delete, *falseStack, *falseA, *forced,
      binMode, optimize, binOutput, *processed, *assigned, count, *used,
      *max, COREcount, RATmode, RATcount, nActive, *lratTable, nLemmas,
      maxRAT, *RATset, *preRAT, maxDependencies, nDependencies, bar,
      backforce, reduce, *dependencies, maxVar, maxSize, mode, verb,
      unitSize, prep, *current, nRemoved, warning, delProof, *setMap,
      *setTruth;
  char *coreStr, *lemmaStr;
  struct timeval start_time;
  long mem_used, time, nClauses, nStep, nOpt, nAlloc, *unitStack, *reason,
      lemmas, nResolve, nReads, nWrites, lratSize, lratAlloc, *lratLookup,
      **wlist, *optproof, *formula, *proof;
};

static inline void assign (struct solver *S, int lit) {
  S->falseA[-lit] = 1;
  *(S->assigned++) = -lit;
}

int compare (const void *a, const void *b) {
  return (*(int *) a - *(int *) b);
}

int abscompare (const void *a, const void *b) {
  return (abs (*(int *) a) - abs (*(int *) b));
}

static inline void printClause (int *clause) {
  printf ("[%i] ", clause[ID]);
  while (*clause)
    printf ("%i ", *clause++);
  printf ("0\n");
}

static inline void addWatchPtr (struct solver *S, int lit, long watch) {
  if (S->used[lit] + 1 == S->max[lit]) {
    S->max[lit] *= 1.5;
    S->wlist[lit] =
        (long *) realloc (S->wlist[lit], sizeof (long) * S->max[lit]);
    //    if (S->max[lit] > 1000) printf("c watchlist %i increased to %i\n",
    //    lit, S->max[lit]);
    if (S->wlist[lit] == NULL) {
      printf ("c MEMOUT: reallocation failed for watch list of %i\n", lit);
      exit (0);
    }
  }
  S->wlist[lit][S->used[lit]++] = watch | S->mask;
  S->wlist[lit][S->used[lit]] = END;
}

static inline void addWatch (struct solver *S, int *clause, int index) {
  addWatchPtr (S, clause[index], ((long) (((clause) -S->DB)) << 1));
}

static inline void removeWatch (struct solver *S, int *clause, int index) {
  int i, lit = clause[index];
  if ((S->used[lit] > INIT) && (S->max[lit] > 2 * S->used[lit])) {
    S->max[lit] = (3 * S->used[lit]) >> 1;
    S->wlist[lit] =
        (long *) realloc (S->wlist[lit], sizeof (long) * S->max[lit]);
    assert (S->wlist[lit] != NULL);
  }
  long *watch = S->wlist[lit];
  for (i = 0; i < S->used[lit]; i++) {
    int *_clause = S->DB + (*(watch++) >> 1);
    if (_clause == clause) {
      watch[-1] = S->wlist[lit][--S->used[lit]];
      S->wlist[lit][S->used[lit]] = END;
      return;
    }
  }
}

static inline void addUnit (struct solver *S, long index) {
  S->unitStack[S->unitSize++] = index;
}

static inline void removeUnit (struct solver *S, int lit) {
  int i, found = 0;
  for (i = 0; i < S->unitSize; i++) {
    if (found)
      S->unitStack[i - 1] = S->unitStack[i];
    if (S->DB[S->unitStack[i]] == lit)
      found = 1;
  }
  S->unitSize--;
}

static inline void unassignUnit (struct solver *S, int lit) {
  if (S->verb)
    printf ("c removing unit %i\n", lit);
  while (S->falseA[-lit]) {
    if (S->verb)
      printf ("c removing unit %i (%i)\n", S->forced[-1], lit);
    S->falseA[*(--S->forced)] = 0;
    S->reason[abs (*S->forced)] = 0;
  }
  S->processed = S->assigned = S->forced;
}

static inline void markWatch (struct solver *S, int *clause, int index,
                              int offset) {
  long *watch = S->wlist[clause[index]];
  for (;;) {
    int *_clause = (S->DB + (*(watch++) >> 1) + (long) offset);
    if (_clause == clause) {
      watch[ID] |= ACTIVE;
      return;
    }
  }
}

static inline void addDependency (struct solver *S, int dep, int forced) {
  if (1 || S->traceFile || S->lratFile) { // temporary for MAXDEP
    if (S->nDependencies == S->maxDependencies) {
      S->maxDependencies = (S->maxDependencies * 3) >> 1;
      //      printf ("c dependencies increased to %i\n",
      //      S->maxDependencies);
      S->dependencies =
          realloc (S->dependencies, sizeof (int) * S->maxDependencies);
      if (S->dependencies == NULL) {
        printf ("c MEMOUT: dependencies reallocation failed\n");
        exit (0);
      }
    }
    //    printf("c adding dep %i\n", (dep << 1) + forced);
    S->dependencies[S->nDependencies++] = (dep << 1) + forced;
  }
}

static inline void markClause (struct solver *S, int *clause, int index) {
  S->nResolve++;
  addDependency (S, clause[index - 1] >> 1, (S->assigned > S->forced));

  if ((clause[index + ID] & ACTIVE) == 0) {
    S->nActive++;
    clause[index + ID] |= ACTIVE;
    if ((S->mode == BACKWARD_UNSAT) && clause[index + 1]) {
      S->optproof[S->nOpt++] =
          (((long) (clause - S->DB) + index) << INFOBITS) + 1;
    }
    if (clause[1 + index] == 0)
      return;
    markWatch (S, clause, index, -index);
    markWatch (S, clause, 1 + index, -index);
  }
  while (*clause)
    S->falseA[*(clause++)] = MARK;
}

void analyze (struct solver *S, int *clause,
              int index) { // Mark all clauses involved in conflict
  markClause (S, clause, index);
  while (S->assigned > S->falseStack) {
    int lit = *(--S->assigned);
    if (S->falseA[lit] == MARK) {
      if (S->reason[abs (lit)]) {
        markClause (S, S->DB + S->reason[abs (lit)], -1);
        if (S->assigned >= S->forced)
          S->reason[abs (lit)] = 0;
      }
    } else if (S->falseA[lit] == ASSUMED && !S->RATmode && S->reduce &&
               !S->lratFile) { // Remove unused literal
      S->nRemoved++;
      int *tmp = S->current;
      while (*tmp != lit)
        tmp++;
      while (*tmp) {
        tmp[0] = tmp[1];
        tmp++;
      }
      tmp[-1] = 0;
    }
    if (S->assigned >= S->forced)
      S->reason[abs (lit)] = 0;
    S->falseA[lit] = (S->assigned < S->forced);
  }

  S->processed = S->assigned = S->forced;
}

void noAnalyze (struct solver *S) {
  while (S->assigned > S->falseStack) {
    int lit = *(--S->assigned);
    if (S->assigned >= S->forced)
      S->reason[abs (lit)] = 0;
    S->falseA[lit] = (S->assigned < S->forced);
  }

  S->processed = S->assigned = S->forced;
}

int propagate (struct solver *S, int init,
               int mark) { // Performs unit propagation (init not used?)
  int *start[2];
  int check = 0, mode = !S->prep;
  int i, lit, _lit = 0;
  long *watch, *_watch;
  start[0] = start[1] = S->processed;
flip_check:;
  check ^= 1;
  while (start[check] < S->assigned) { // While unprocessed false literals
    lit = *(start[check]++);           // Get first unprocessed literal
    if (lit == _lit)
      watch = _watch;
    else
      watch = S->wlist[lit]; // Obtain the first watch pointer
    while (*watch !=
           END) { // While there are watched clauses (watched by lit)
      if ((*watch & mode) != check) {
        watch++;
        continue;
      }
      int *clause = S->DB + (*watch >> 1); // Get the clause from DB
      if (S->falseA[-clause[0]] || S->falseA[-clause[1]]) {
        watch++;
        continue;
      }
      if (clause[0] == lit)
        clause[0] =
            clause[1]; // Ensure that the other watched literal is in front
      for (i = 2; clause[i]; ++i) // Scan the non-watched literals
        if (S->falseA[clause[i]] ==
            0) { // When clause[j] is not false, it is either true or unset
          clause[1] = clause[i];
          clause[i] = lit; // Swap literals
          addWatchPtr (S, clause[1],
                       *watch); // Add the watch to the list of clause[1]
          *watch = S->wlist[lit][--S->used[lit]]; // Remove pointer
          S->wlist[lit][S->used[lit]] = END;
          goto next_clause;
        } // Goto the next watched clause
      clause[1] = lit;
      watch++; // Set lit at clause[1] and set next watch
      if (!S->falseA[clause[0]]) { // If the other watched literal is
                                   // falsified,
        assign (S,
                clause[0]); // A unit clause is found, and the reason is set
        S->reason[abs (clause[0])] = ((long) ((clause) -S->DB)) + 1;
        if (!check) {
          start[0]--;
          _lit = lit;
          _watch = watch;
          goto flip_check;
        }
      } else if (!mark) {
        noAnalyze (S);
        return UNSAT;
      } else {
        analyze (S, clause, 0);
        return UNSAT;
      } // Found a root level conflict -> UNSAT
    next_clause:;
    }
  } // Set position for next clause
  if (check)
    goto flip_check;
  S->processed = S->assigned;
  return SAT;
} // Finally, no conflict was found

// Propagate top level units
static inline int propagateUnits (struct solver *S, int init) {
  int i;
  //  printf("c propagateUnits %i\n", S->unitSize);
  while (S->forced > S->falseStack) {
    S->falseA[*(--S->forced)] = 0;
    S->reason[abs (*S->forced)] = 0;
  }
  S->forced = S->assigned = S->processed = S->falseStack;
  for (i = 0; i < S->unitSize; i++) {
    int lit = S->DB[S->unitStack[i]];
    S->reason[abs (lit)] = S->unitStack[i] + 1;
    assign (S, lit);
  }

  if (propagate (S, init, 1) == UNSAT) {
    return UNSAT;
  }
  S->forced = S->processed;
  return SAT;
}

// Put falsified literals at the end and returns the size under the current
// assignment: negative size means satisfied, size = 0 means falsified
int sortSize (struct solver *S, int *lemma) {
  unsigned int size = 0, last = 0, sat = 1;
  while (lemma[last]) {
    int lit = lemma[last++];
    if (S->falseA[lit] == 0) {
      if (S->falseA[-lit])
        sat = -1;
      lemma[last - 1] = lemma[size];
      lemma[size++] = lit;
    }
  }
  return sat * size;
}

// print the core clauses to coreFile in DIMACS format
void printCore (struct solver *S) {
  int i, j;
  for (i = 0; i < S->nClauses; i++) {
    int *clause = S->DB + (S->formula[i] >> INFOBITS);
    if (clause[ID] & ACTIVE)
      S->COREcount++;
  }
  printf ("c %i of %li clauses in core                            \n",
          S->COREcount, S->nClauses);

  if (S->coreStr) {
    FILE *coreFile = fopen (S->coreStr, "w");
    fprintf (coreFile, "p cnf %i %i\n", S->nVars, S->COREcount);
    for (i = 0; i < S->nClauses; i++) {
      int *clause = S->DB + (S->formula[i] >> INFOBITS);
      if (clause[ID] & ACTIVE) {
        while (*clause)
          fprintf (coreFile, "%i ", *clause++);
        fprintf (coreFile, "0\n");
      }
    }
    fclose (coreFile);
  }
}

void write_lit (struct solver *S, int lit) { // change to long?
  unsigned int l = abs (lit) << 1;
  if (lit < 0)
    l++;

  do {
    if (l <= 127) {
      fputc ((char) l, S->lratFile);
    } else {
      fputc ((char) (128 + (l & 127)), S->lratFile);
    }
    S->nWrites++;
    l = l >> 7;
  } while (l);
}

void printLRATline (struct solver *S, int time) {
  int *line = S->lratTable + S->lratLookup[time];
  if (S->binOutput) {
    fputc ('a', S->lratFile);
    S->nWrites++;
    while (*line)
      write_lit (S, *line++);
    write_lit (S, *line++);
    while (*line)
      write_lit (S, *line++);
    write_lit (S, *line++);
  } else {
    while (*line)
      fprintf (S->lratFile, "%i ", *line++);
    fprintf (S->lratFile, "%i ", *line++);
    while (*line)
      fprintf (S->lratFile, "%i ", *line++);
    fprintf (S->lratFile, "%i\n", *line++);
  }
}

// print the core lemmas to lemmaFile in DRAT format
void printProof (struct solver *S) {
  int step;
  printf ("c %i of %i lemmas in core using %lu resolution steps\n",
          S->nActive - S->COREcount + 1, S->nLemmas + 1, S->nResolve);
  printf ("c %d RAT lemmas in core; %i redundant literals in core lemmas\n",
          S->RATcount, S->nRemoved);

  // NB: not yet working with forward checking
  if (S->mode == FORWARD_UNSAT) {
    printf ("c optimized proofs are not supported for forward checking\n");
    return;
  }

  // replace S->proof by S->optproof
  if (S->mode == BACKWARD_UNSAT) {
    if (S->nOpt > S->nAlloc) {
      S->nAlloc = S->nOpt;
      S->proof = (long *) realloc (S->proof, sizeof (long) * S->nAlloc);
      if (S->proof == NULL) {
        printf ("c MEMOUT: reallocation of proof list failed\n");
        exit (0);
      }
    }
    S->nStep = 0;
    S->nLemmas = 0;
    for (step = S->nOpt - 1; step >= 0; step--) {
      long ad = S->optproof[step];
      int *lemmas = S->DB + (ad >> INFOBITS);
      if ((ad & 1) == 0)
        S->nLemmas++;
      //      if (lemmas[ID] & ACTIVE) lemmas[ID] ^= ACTIVE; // only useful
      //      for checking multiple times?
      S->proof[S->nStep++] = S->optproof[step];
    }
  } // why not reuse ad?

  if (S->lemmaStr) {
    FILE *lemmaFile = fopen (S->lemmaStr, "w");
    for (step = 0; step < S->nStep; step++) {
      long ad = S->proof[step];
      int *lemmas = S->DB + (ad >> INFOBITS);
      if (!lemmas[1] && (ad & 1))
        continue; // don't delete unit clauses
      if (ad & 1)
        fprintf (lemmaFile, "d ");
      int reslit = lemmas[PIVOT];
      while (*lemmas) {
        int lit = *lemmas++;
        if (lit == reslit)
          fprintf (lemmaFile, "%i ", lit);
      }
      lemmas = S->DB + (ad >> INFOBITS);
      while (*lemmas) {
        int lit = *lemmas++;
        if (lit != reslit)
          fprintf (lemmaFile, "%i ", lit);
      }
      fprintf (lemmaFile, "0\n");
    }
    fprintf (lemmaFile, "0\n");
    fclose (lemmaFile);
  }

  if (S->lratFile) {
    int lastAdded = S->nClauses;
    int flag = 0;
    for (step = 0; step < S->nStep; step++) {
      long ad = S->proof[step];
      int *lemmas = S->DB + (ad >> INFOBITS);
      if ((ad & 1) == 0) {
        if (lastAdded == 0) {
          if (S->binOutput) {
            write_lit (S, 0);
          } else {
            fprintf (S->lratFile, "0\n");
          }
        }
        lastAdded = lemmas[ID] >> 1;
        printLRATline (S, lastAdded);
      } else if (lastAdded == S->nClauses)
        continue;
      else if (!lemmas[1] && (ad & 1))
        continue; // don't delete unit clauses
      else if (ad & 1) {
        if (lastAdded != 0) {
          if (S->binOutput) {
            fputc ('d', S->lratFile);
            S->nWrites++;
          } else {
            fprintf (S->lratFile, "%i d ", lastAdded);
          }
        }
        lastAdded = 0;
        if (S->binOutput) {
          write_lit (S, lemmas[ID] >> 1);
        } else {
          fprintf (S->lratFile, "%i ", lemmas[ID] >> 1);
        }
      }
    }
    if (lastAdded != S->nClauses) {
      if (S->binOutput) {
        write_lit (S, 0);
      } else {
        fprintf (S->lratFile, "0\n");
      }
    }

    printLRATline (S, S->count);

    fclose (S->lratFile);
    if (S->nWrites)
      printf ("c wrote optimized proof in LRAT format of %li bytes\n",
              S->nWrites);
  }
}

void printNoCore (struct solver *S) {
  if (S->lratFile) {
    if (S->binOutput) {
      fputc ('d', S->lratFile);
      S->nWrites++;
    } else {
      fprintf (S->lratFile, "%ld d ", S->nClauses);
    }
    int i;
    for (i = 0; i < S->nClauses; i++) {
      int *clause = S->DB + (S->formula[i] >> INFOBITS);
      if ((clause[ID] & ACTIVE) == 0) {
        if (S->binOutput) {
          write_lit (S, clause[ID] >> 1);
        } else {
          fprintf (S->lratFile, "%i ", clause[ID] >> 1);
        }
      }
    }
    if (S->binOutput) {
      write_lit (S, 0);
    } else {
      fprintf (S->lratFile, "0\n");
    }
  }
}

// print the dependency graph to traceFile in TraceCheck+ format
// this procedure adds the active clauses at the end of the trace
void printTrace (struct solver *S) {
  if (S->traceFile) {
    int i;
    for (i = 0; i < S->nClauses; i++) {
      int *clause = S->DB + (S->formula[i] >> INFOBITS);
      if (clause[ID] & ACTIVE) {
        fprintf (S->traceFile, "%i ", i + 1);
        while (*clause)
          fprintf (S->traceFile, "%i ", *clause++);
        fprintf (S->traceFile, "0 0\n");
      }
    }
    fclose (S->traceFile);
  }
}

void printActive (struct solver *S) {
  int i, j;
  if (S->activeFile) {
    for (i = -S->maxVar; i <= S->maxVar; i++)
      if (i != 0)
        for (j = 0; j < S->used[i]; j++) {
          int *clause = S->DB + (S->wlist[i][j] >> 1);
          if (*clause == i) {
            while (*clause)
              fprintf (S->activeFile, "%i ", *clause++);
            fprintf (S->activeFile, "0\n");
          }
        }
  }
}

void postprocess (struct solver *S) {
  printNoCore (S); // print before proof optimization
  printActive (S);
  printCore (S);
  printTrace (S); // closes traceFile
  printProof (S);
} // closes lratFile

void lratAdd (struct solver *S, int elem) {
  if (S->lratSize == S->lratAlloc) {
    S->lratAlloc = S->lratAlloc * 3 >> 1;
    S->lratTable =
        (int *) realloc (S->lratTable, sizeof (int) * S->lratAlloc);
  }
  S->lratTable[S->lratSize++] = elem;
}

void printDependenciesFile (struct solver *S, int *clause, int RATflag,
                            int mode) {
  FILE *file = NULL;
  if (mode == 0)
    file = S->traceFile;
  if (mode == 1)
    file = S->lratFile;

  if (file) {
    int i, j, k;
    int tmp = S->lratSize;

    if (clause != NULL) {
      S->lratLookup[clause[ID] >> 1] = S->lratSize;
    } else {
      S->lratLookup[S->count] = S->lratSize;
    }

    if (clause != NULL) {
      int size = 0;
      int *sortClause;
      sortClause = (int *) malloc (sizeof (int) * S->maxSize);
      lratAdd (S, S->time >> 1); // NB: long to ing
      int reslit = clause[PIVOT];
      while (*clause) {
        if (*clause == reslit)
          lratAdd (S, reslit);
        sortClause[size++] = *clause++;
      }
      qsort (sortClause, size, sizeof (int), abscompare);
      for (i = 0; i < size; i++) {
        int lit = sortClause[i];
        if (lit != reslit)
          lratAdd (S, lit);
      }
    } else {
      lratAdd (S, S->count);
    }
    lratAdd (S, 0);

    int isRUP = 1;
    for (i = 0; i < S->nDependencies; i++)
      if (S->dependencies[i] < 0) {
        isRUP = 0;
        break;
      }

    if (isRUP) {
      for (i = S->nDependencies - 1; i >= 0; i--)
        lratAdd (S, S->dependencies[i] >> 1);
      lratAdd (S, 0);
      goto printLine;
    }

    // first print the preRAT units in order of becoming unit
    int size = 0;
    for (i = 0; i < S->nDependencies; i++) {
      if (S->dependencies[i] > 0)
        continue;
      for (j = i - 1; j >= 0 && S->dependencies[j] > 0; j--) {
        int flag = 0;
        int cls = S->dependencies[j];
        if (cls & 1)
          continue;
        for (k = 0; k < size; k++)
          if (S->preRAT[k] == cls)
            flag = 1;
        if (!flag) {
          S->preRAT[size++] = cls;
          lratAdd (S, cls >> 1);
        }
      }
    }

    // print dependencies in order of becoming unit
    for (i = S->nDependencies - 1; i >= 0; i--) {
      int cls = S->dependencies[i];
      if ((mode == 0) && (cls < 0))
        continue;
      if (mode == 0) {
        int flag = 0;
        for (j = 0; j < size; j++)
          if (S->preRAT[j] == cls)
            flag = 1;
        if (!flag) {
          S->preRAT[size++] = cls;
          lratAdd (S, cls >> 1);
        }
      }
      if ((mode == 1) && (cls & 1))
        lratAdd (S, cls >> 1);
    }
    lratAdd (S, 0);

  printLine:;
    if (mode == 0) {
      for (i = tmp; i < S->lratSize; i++)
        fprintf (file, "%d ", S->lratTable[i]);
      S->lratSize = tmp;
      fprintf (file, "\n");
    }
  }
}

void printDependencies (struct solver *S, int *clause, int RATflag) {
  if (clause != NULL) {
    int i;
    clause[MAXDEP] = 0;
    for (i = 0; i < S->nDependencies; i++) {
      //      printf ("%i ", S->dependencies[i]);
      if (S->dependencies[i] > clause[MAXDEP])
        clause[MAXDEP] = S->dependencies[i];
    }
    //    printf("\n%i :", clause[MAXDEP]);
    //    printClause(clause);
    assert (clause[MAXDEP] < clause[ID]);
  }

  printDependenciesFile (S, clause, RATflag, 0);
  printDependenciesFile (S, clause, RATflag, 1);
}

int checkRAT (struct solver *S, int pivot, int mark) {
  int i, j, nRAT = 0;

  // Loop over all literals to calculate resolution candidates
  for (i = -S->maxVar; i <= S->maxVar; i++) {
    if (i == 0)
      continue;
    // Loop over all watched clauses for literal
    for (j = 0; j < S->used[i]; j++) {
      int *watched = S->DB + (S->wlist[i][j] >> 1);
      int id = watched[ID] >> 1;
      int active = watched[ID] & ACTIVE;
      if (*watched == i) { // If watched literal is in first position
        while (*watched)
          if (*watched++ == -pivot) {
            if ((S->mode == BACKWARD_UNSAT) && !active) {
              //              printf ("c RAT check ignores unmarked clause :
              //              "); printClause (S->DB + (S->wlist[i][j] >>
              //              1));
              continue;
            }
            if (nRAT == S->maxRAT) {
              S->maxRAT = (S->maxRAT * 3) >> 1;
              S->RATset = realloc (S->RATset, sizeof (int) * S->maxRAT);
              assert (S->RATset != NULL);
            }
            S->RATset[nRAT++] = S->wlist[i][j] >> 1;
            break;
          }
      }
    }
  }

  // S->prep = 1;
  // Check all clauses in RATset for RUP
  int flag = 1;
  qsort (S->RATset, nRAT, sizeof (int), compare);
  S->nDependencies = 0;
  for (i = nRAT - 1; i >= 0; i--) {
    int *RATcls = S->DB + S->RATset[i];
    int id = RATcls[ID] >> 1;
    int blocked = 0;
    long int reason = 0;
    if (S->verb) {
      printf ("c RAT clause: ");
      printClause (RATcls);
    }

    while (*RATcls) {
      int lit = *RATcls++;
      if (lit != -pivot && S->falseA[-lit])
        if (!blocked || reason > S->reason[abs (lit)])
          blocked = lit, reason = S->reason[abs (lit)];
    }

    if (blocked && reason) {
      analyze (S, S->DB + reason, -1);
      S->reason[abs (blocked)] = 0;
    }

    if (!blocked) {
      RATcls = S->DB + S->RATset[i];
      while (*RATcls) {
        int lit = *RATcls++;
        if (lit != -pivot && !S->falseA[lit]) {
          assign (S, -lit);
          S->reason[abs (lit)] = 0;
        }
      }
      if (propagate (S, 0, mark) == SAT) {
        flag = 0;
        break;
      }
    }
    addDependency (S, -id, 1);
  }

  if (flag == 0) {
    while (S->forced < S->assigned) {
      S->falseA[*(--S->assigned)] = 0;
      S->reason[abs (*S->assigned)] = 0;
    }
    if (S->verb)
      printf ("c RAT check on pivot %i failed\n", pivot);
    return FAILED;
  }

  return SUCCESS;
}

int setUCP (struct solver *S, int *cnf, int *trail) {
  int touched = 0, satisfied = 1;
  int *clause = cnf;

  while (*clause) {
    int *literals = clause;
    int unit = 0, sat = 0, und = 0;
    int i;
    while (*literals) {
      int lit = *literals++;
      if (S->setTruth[lit] == 1) {
        sat = 1;
      }
      if (S->setTruth[lit] == 0) {
        und++;
        unit = lit;
      }
    }
    clause = literals + 1;
    if (!sat && und == 1) {
      sat = 1;
      touched = 1;
      *trail++ = unit;
      *trail = 0;
      if (S->verb)
        printf ("c found unit %i\n", unit);
      S->setTruth[unit] = 1;
      S->setTruth[-unit] = -1;
    }
    satisfied &= sat;
    if (!sat && !und)
      return FAILED;
  }

  *trail = 0;
  if (satisfied)
    return SUCCESS;
  if (touched)
    return setUCP (S, cnf, trail);
  return FIXPOINT;
}

/*
int setDLL (struct solver *S, int *cnf, int *trail) {
  int res = setUCP (S, cnf, trail);
  if (res == SUCCESS) return SUCCESS;
  if (res == FAILED ) return FAILED;
  while (*trail) trail++;

  int decision = 1;
  while (S->setTruth[decision]) decision++;

  *trail++ = decision;
  *trail   = 0;
  S->setTruth[ decision] =  1;
  S->setTruth[-decision] = -1;

  if (S->verb) printf("c branch on %i\n", decision);
  if (setDLL (S, cnf, trail) == SUCCESS) return SUCCESS;

  while (*trail) trail++;
  while (*trail != decision) {
    S->setTruth[ *trail] = 0;
    S->setTruth[-*trail] = 0;
    trail--; }

  *trail++ = -decision;
  *trail = 0;
  S->setTruth[ decision] = -1;
  S->setTruth[-decision] =  1;

  if (S->verb) printf("c branch on %i\n", -decision);
  return setDLL (S, cnf, trail); }

int setRedundancyCheck (struct solver *S, int *clause, int size, int uni) {
  int i, j, blocked, nSPR = 0;
  long int reason;

  int *trail = (int*) malloc (sizeof(int) * (size + 1));

  if (S->verb) printf("c starting SPR check\n");

  for (i = 1; i <= size; i++) {
    trail            [i - 1]  =  0;
    S->setMap[ clause[i - 1]] =  i;
    S->setMap[-clause[i - 1]] = -i; }

  // Loop over all literals to calculate resolution candidates
  for (i = -S->maxVar; i <= S->maxVar; i++) {
    if (i == 0) continue;
    // Loop over all watched clauses for literal
    for (j = 0; j < S->used[i]; j++) {
      int* watchedClause = S->DB + (S->wlist[i][j] >> 1);
      if (*watchedClause == i) { // If watched literal is in first position
        int flag = 0;
        blocked = 0;
        reason = 0;
        while (*watchedClause) {
          int lit = *watchedClause++;
          if (S->setMap[lit] < 0) flag = 1;
          else if (!S->setMap[lit] && S->falseA[-lit]) {
            if (blocked == 0 || reason > S->reason[ abs(lit) ])
              blocked = lit, reason = S->reason[ abs(lit) ]; } }

       if (blocked != 0 && reason != 0 && flag == 1) {
         analyze (S, S->DB + reason, -1); S->reason[abs(blocked)] = 0; }

       // If resolution candidate, add to list
       if (blocked == 0 && flag == 1) {
         if (nSPR == S->maxRAT) {
           S->maxRAT = (S->maxRAT * 3) >> 1;
           S->RATset = realloc(S->RATset, sizeof(int) * S->maxRAT); }
         S->RATset[nSPR++] = S->wlist[i][j] >> 1; } } } }

  // Check all candidates for RUP
  int cnfSize = size + 2; // first clause + terminating zero
  int filtered = 0;
  for (i = 0; i < nSPR; i++) {
    int inSet = 1;
    int* candidate = S->DB + S->resolutionCandidates[i];
    if (S->verb) {
      printf("c candidate: "); printLiterals (candidate); }
    while (*candidate) { int lit = *candidate++;
      if (S->setMap[lit]) inSet++;
      if (!S->setMap[lit] && !S->falseA[lit]) {
        ASSIGN(-lit); S->reason[abs(lit)] = 0; } }
    if (propagate (S, 0) == SAT) {
      if (S->verb) printf(" FAILED\n");
      cnfSize += inSet;
      S->processed = S->forced;
      while (S->forced < S->assigned) S->falseA[*(--S->assigned)] = 0;
      S->resolutionCandidates[filtered++] = S->resolutionCandidates[i]; }
    else {
      if (S->verb) printf(" SUCCESS\n"); } }

  int *cnf = (int*) malloc (sizeof(int) * cnfSize);
  int *tmp = cnf;
  for (i = 1; i <= size; i++) *tmp++ = i;
  *tmp++ = 0;
  numCandidates = filtered;
  for (i = 0; i < numCandidates; i++) {
    int* candidate = S->DB + S->resolutionCandidates[i];
    while (*candidate) {
      int lit = *candidate++;
      if (S->setMap[lit]) *tmp++ = S->setMap[lit]; }
    *tmp++ = 0; }
  *tmp++ = 0;

  if (S->verb) {
    tmp = cnf;
    printf("c printing CNF:\n");
    while (*tmp) {
      int *clause = tmp;
      printf("c ");
      while (*clause) printf("%i ", *clause++);
      printf("\n");
      tmp = clause + 1; } }

  int res = setDLL (S, cnf, trail);
  if (S->verb) {
    if (res == SUCCESS) printf("c SUCCESS\n");
    if (res == FAILED ) printf("c FAILED\n"); }

  for (i = 1; i <= size; i++) {
    S->setMap[ clause[i - 1]] = 0;
    S->setMap[-clause[i - 1]] = 0;
    S->setTruth[  i ]         = 0;
    S->setTruth[ -i ]         = 0; }

  free(trail);
  free( cnf );
  return res; }
*/

int redundancyCheck (struct solver *S, int *clause, int size, int mark) {
  int i, indegree;
  int falsePivot = S->falseA[clause[PIVOT]];
  if (S->verb) {
    printf ("c checking lemma (%i, %i) ", size, clause[PIVOT]);
    printClause (clause);
  }

  if (S->mode != FORWARD_UNSAT) {
    if ((clause[ID] & ACTIVE) == 0)
      return SUCCESS;
  } // redundant?
    //    clause[PIVOT] ^= ACTIVE; }

  if (size < 0) {
    S->DB[S->reason[abs (*clause)] - 2] |= 1;
    return SUCCESS;
  }

  indegree = S->nResolve;

  S->RATmode = 0;
  S->nDependencies = 0;
  for (i = 0; i < size; ++i) {
    if (S->falseA[-clause[i]]) { // should only occur in forward mode
      if (S->warning != NOWARNING) {
        printf ("c WARNING: found a tautological clause in proof: ");
        printClause (clause);
      }
      if (S->warning == HARDWARNING)
        exit (HARDWARNING);
      while (S->forced < S->assigned) {
        S->falseA[*(--S->assigned)] = 0;
        S->reason[abs (*S->assigned)] = 0;
      }
      return SUCCESS;
    }
    S->falseA[clause[i]] = ASSUMED;
    *(S->assigned++) = clause[i];
    S->reason[abs (clause[i])] = 0;
  }

  S->current = clause;
  if (propagate (S, 0, mark) == UNSAT) {
    indegree = S->nResolve - indegree;
    if (indegree <= 2 && S->prep == 0) {
      S->prep = 1;
      if (S->verb)
        printf ("c [%li] preprocessing checking mode on\n", S->time);
    }
    if (indegree > 2 && S->prep == 1) {
      S->prep = 0;
      if (S->verb)
        printf ("c [%li] preprocessing checking mode off\n", S->time);
    }
    if (S->verb)
      printf ("c lemma has RUP\n");
    printDependencies (S, clause, 0);
    return SUCCESS;
  }

  // Failed RUP check.  Now test RAT.
  // printf ("RUP check failed.  Starting RAT check.\n");
  int reslit = clause[PIVOT];
  if (S->verb)
    printf ("c RUP checked failed; starting RAT check on pivot %d.\n",
            reslit);

  if (falsePivot)
    return FAILED;

  int *savedForced = S->forced;

  S->RATmode = 1;
  S->forced = S->assigned;

  int failed = 0;
  if (checkRAT (S, reslit, mark) == FAILED) {
    failed = 1;
    if (S->warning != NOWARNING) {
      printf ("c WARNING: RAT check on proof pivot failed : ");
      printClause (clause);
    }
    if (S->warning == HARDWARNING)
      exit (HARDWARNING);
    for (i = 0; i < size; i++) {
      if (clause[i] == reslit)
        continue;
      if (checkRAT (S, clause[i], mark) == SUCCESS) {
        clause[PIVOT] = clause[i];
        failed = 0;
        break;
      }
    }
  }

  if (failed == 0)
    printDependencies (S, clause, 1);

  S->processed = S->forced = savedForced;
  while (S->forced < S->assigned) {
    S->falseA[*(--S->assigned)] = 0;
    S->reason[abs (*S->assigned)] = 0;
  }

  if (failed) {
    printf ("c RAT check failed on all possible pivots\n");
    return FAILED;
  }

  if (mark)
    S->RATcount++;
  if (S->verb)
    printf ("c lemma has RAT on %i\n", clause[PIVOT]);
  return SUCCESS;
}

int init (struct solver *S) {
  S->forced = S->falseStack; // Points inside *falseStack at first decision
                             // (unforced literal)
  S->processed = S->falseStack; // Points inside *falseStack at first
                                // unprocessed literal
  S->assigned = S->falseStack;  // Points inside *falseStack at last
                                // unprocessed literal

  // initialize watch pointers on the original clauses
  S->RATmode = 0;
  S->nRemoved = 0;
  S->nOpt = 0;
  S->nResolve = 0;
  S->RATcount = 0;
  S->nActive = 0;
  S->COREcount = 0;
  S->unitSize = 0;

  int i;
  for (i = 1; i <= S->maxVar; ++i) {
    S->reason[i] = 0;
    S->falseStack[i] = 0;
    S->falseA[i] = S->falseA[-i] = 0;
    S->used[i] = S->used[-i] = 0;
    S->wlist[i][0] = S->wlist[-i][0] = END;
  }

  for (i = 0; i < S->nClauses; i++) {
    int *clause = S->DB + (S->formula[i] >> INFOBITS);
    if (clause[ID] & ACTIVE)
      clause[ID] ^= ACTIVE;
    if (clause[0] == 0) {
      printf ("c formula contains empty clause\n");
      if (S->coreStr) {
        FILE *coreFile = fopen (S->coreStr, "w");
        fprintf (coreFile, "p cnf 0 1\n 0\n");
        fclose (coreFile);
      }
      if (S->lemmaStr) {
        FILE *lemmaFile = fopen (S->lemmaStr, "w");
        fprintf (lemmaFile, "0\n");
        fclose (lemmaFile);
      }
      return UNSAT;
    }
    if (clause[1]) {
      addWatch (S, clause, 0);
      addWatch (S, clause, 1);
    } else if (S->falseA[clause[0]]) {
      printf ("c found complementary unit clauses\n");
      if (S->coreStr) {
        FILE *coreFile = fopen (S->coreStr, "w");
        fprintf (coreFile, "p cnf %i 2\n%i 0\n%i 0\n", abs (clause[0]),
                 clause[0], -clause[0]);
        fclose (coreFile);
      }
      if (S->lemmaStr) {
        FILE *lemmaFile = fopen (S->lemmaStr, "w");
        fprintf (lemmaFile, "0\n");
        fclose (lemmaFile);
      }
      if (S->lratFile) {
        int j;
        for (j = 0; j < i; j++) {
          int *_clause = S->DB + (S->formula[j] >> INFOBITS);
          if ((_clause[0] == -clause[0]) && !_clause[1])
            break;
        }
        fprintf (S->lratFile, "%li 0 %i %i 0\n", S->nClauses + 1, j + 1,
                 i + 1);
      }
      return UNSAT;
    } else if (!S->falseA[-clause[0]]) {
      addUnit (S, (long) (clause - S->DB));
      assign (S, clause[0]);
    }
  }

  S->nDependencies = 0;
  S->time = S->count; // Alternative time init
  if (propagateUnits (S, 1) == UNSAT) {
    printf ("c UNSAT via unit propagation on the input instance\n");
    printDependencies (S, NULL, 0);
    postprocess (S);
    return UNSAT;
  }
  return SAT;
}

int verify (struct solver *S, int begin, int end) {
  int top_flag = 1;
  if (init (S) == UNSAT)
    return UNSAT;

  if (S->mode == FORWARD_UNSAT) {
    if (begin == end)
      printf ("c start forward verification\n");
  }

  int step;
  int adds = 0;
  int active = S->nClauses;
  for (step = 0; step < S->nStep; step++) {
    if (step >= begin && step < end)
      continue;
    long ad = S->proof[step];
    long d = ad & 1;
    int *lemmas = S->DB + (ad >> INFOBITS);

    S->time = lemmas[ID];
    if (d) {
      active--;
    } else {
      active++;
      adds++;
    }
    if (S->mode == FORWARD_SAT && S->verb)
      printf ("c %i active clauses\n", active);

    if (!lemmas[1]) { // found a unit
      int lit = lemmas[0];
      if (S->verb)
        printf ("c found unit in proof %i [%li]\n", lit, S->time);
      if (d) {
        if (S->mode == FORWARD_SAT) {
          removeUnit (S, lit);
          propagateUnits (S, 0);
        } else { // no need to remove units while checking UNSAT
          if (S->verb) {
            printf ("c removing proof step: d ");
            printClause (lemmas);
          }
          S->proof[step] = 0;
          continue;
        }
      } else {
        if (S->mode == BACKWARD_UNSAT && S->falseA[-lit]) {
          S->proof[step] = 0;
          continue;
        } else {
          addUnit (S, (long) (lemmas - S->DB));
        }
      }
    }

    if (d && lemmas[1]) { // if delete and not unit
      if ((S->reason[abs (lemmas[0])] - 1) ==
          (lemmas - S->DB)) {         // what is this check?
        if (S->mode != FORWARD_SAT) { // ignore pseudo unit clause deletion
          if (S->verb) {
            printf ("c ignoring deletion instruction %li: ",
                    (lemmas - S->DB));
            printClause (lemmas);
          }
          //        if (S->mode == BACKWARD_UNSAT) { // ignore pseudo unit
          //        clause deletion
          S->proof[step] = 0;
        } else { // if (S->mode == FORWARD_SAT) { // also for FORWARD_UNSAT?
          removeWatch (S, lemmas, 0), removeWatch (S, lemmas, 1);
          propagateUnits (S, 0);
        }
      } else {
        removeWatch (S, lemmas, 0), removeWatch (S, lemmas, 1);
      }
      if (S->mode == FORWARD_UNSAT)
        continue; // Ignore deletion of top-level units
      if (S->mode == BACKWARD_UNSAT)
        continue;
    }

    int size = sortSize (S, lemmas); // after removal of watches

    if (d && S->mode == FORWARD_SAT) {
      if (size == -1)
        propagateUnits (S, 0); // necessary?
      if (redundancyCheck (S, lemmas, size, 1) == FAILED) {
        printf ("c failed at proof line %i (modulo deletion errors)\n",
                step + 1);
        return SAT;
      }
      continue;
    }

    if (d == 0 && S->mode == FORWARD_UNSAT) {
      if (step > end) {
        if (size < 0)
          continue; // Fix of bus error: 10
        if (redundancyCheck (S, lemmas, size, 1) == FAILED) {
          printf ("c failed at proof line %i (modulo deletion errors)\n",
                  step + 1);
          return SAT;
        }

        size = sortSize (S, lemmas);
        S->nDependencies = 0;
      }
    }

    if (lemmas[1])
      addWatch (S, lemmas, 0), addWatch (S, lemmas, 1);

    if (size == 0) {
      printf ("c conflict claimed, but not detected\n");
      return SAT;
    } // change to FAILED?
    if (size == 1) {
      if (S->verb)
        printf ("c found unit %i\n", lemmas[0]);
      assign (S, lemmas[0]);
      S->reason[abs (lemmas[0])] = ((long) ((lemmas) -S->DB)) + 1;
      if (propagate (S, 1, 1) == UNSAT)
        goto start_verification;
      S->forced = S->processed;
    }
  }

  if (S->mode == FORWARD_SAT && active == 0) {
    postprocess (S);
    return UNSAT;
  }

  if (S->mode == FORWARD_UNSAT) {
    if (begin == end) {
      postprocess (S);
      printf ("c ERROR: all lemmas verified, but no conflict\n");
    }
    return SAT;
  }

  if (S->mode == BACKWARD_UNSAT) {
    if (S->backforce) {
      int s;
      for (s = 0; s < step; s++) {
        long ad = S->proof[s];
        int *clause = S->DB + (ad >> INFOBITS);
        if (sortSize (S, clause) >= 0) {
          if ((ad & 1) && (clause[ID] & 1))
            clause[ID] ^= ACTIVE;
          if (!(ad & 1))
            clause[ID] |= ACTIVE;
        }
      }
    }
    if (!S->backforce) {
      printf ("c ERROR: no conflict\n");
      return SAT;
    }
  }

start_verification:;
  if (S->mode == FORWARD_UNSAT) {
    printDependencies (S, NULL, 0);
    postprocess (S);
    return UNSAT;
  }

  if (!S->backforce)
    printDependencies (S, NULL, 0);

  if (S->mode == FORWARD_SAT) {
    printf ("c ERROR: found empty clause during SAT check\n");
    exit (0);
  }
  printf ("c detected empty clause; start verification via backward "
          "checking\n");

  S->forced = S->processed;
  assert (S->mode ==
          BACKWARD_UNSAT); // only reachable in BACKWARD_UNSAT mode

  S->nOpt = 0;

  int checked = 0, skipped = 0;

  double max = (double) adds;

  struct timeval backward_time;
  gettimeofday (&backward_time, NULL);
  for (; step >= 0; step--) {
    struct timeval current_time;
    gettimeofday (&current_time, NULL);
    int seconds = (int) (current_time.tv_sec - S->start_time.tv_sec);
    if ((seconds > S->timeout) && (S->optimize == 0))
      printf ("s TIMEOUT\n"), exit (0);

    if (S->bar)
      if ((adds % 1000) == 0) {
        int f;
        long runtime =
            (current_time.tv_sec - backward_time.tv_sec) * 1000000 +
            (current_time.tv_usec - backward_time.tv_usec);
        double time = (double) (runtime / 1000000.0);
        double fraction = (adds * 1.0) / max;
        printf ("c %.2f%% [", 100.0 * (1.0 - fraction));
        for (f = 1; f <= 20; f++) {
          if ((1.0 - fraction) * 20.0 < 1.0 * f)
            printf (" ");
          else
            printf ("=");
        }
        printf ("] time remaining: %.2f seconds ",
                time / (1.0 - fraction) - time);
        if (step == 0)
          printf ("\n");
        fflush (stdout);
      }

    long ad = S->proof[step];
    long d = ad & 1;
    int *clause = S->DB + (ad >> INFOBITS);

    if (ad == 0)
      continue; // Skip lemma that has been removed from proof
    if (d == 0) {
      adds--;
      if (clause[1]) {
        removeWatch (S, clause, 0), removeWatch (S, clause, 1);
        if (S->reason[abs (clause[0])] ==
            (clause + 1 - S->DB)) { // use this check also for units?
          unassignUnit (S, clause[0]);
        }
      } else
        unassignUnit (S, clause[0]);
    }

    int size = sortSize (S, clause);

    if (d) {
      if (S->verb) {
        printf ("c adding clause (%i) ", size);
        printClause (clause);
      }
      addWatch (S, clause, 0), addWatch (S, clause, 1);
      continue;
    }

    S->time = clause[ID];
    if ((S->time & ACTIVE) == 0) {
      skipped++;
      //      if ((skipped % 100) == 0) printf("c skipped %i, checked %i\n",
      //      skipped, checked);
      continue;
    } // If not marked, continue

    assert (size >= 1);
    int *_clause = clause + size;
    while (*_clause++) {
      S->nRemoved++;
    }
    clause[size] = 0;

    if (S->verb) {
      printf ("c validating clause (%i, %i):  ", clause[PIVOT], size);
      printClause (clause);
    }
    /*
        int i;
        if (size > 1 && (top_flag == 1)) {
          int last = clause[size - 1];
          int pivot = clause[PIVOT];
          for (i = 0; i < size; i++) {
            int tmp = clause[i];
            clause[i] = last;
            clause[size - 1] = 0;
            if (tmp == pivot) clause[PIVOT] = clause[0];
            if (redundancyCheck (S, clause, size - 1, 0) != FAILED) {
              top_flag = 0;
              size = size - 1; break; }
            else {
              clause[i] = tmp;
              clause[size - 1] = last; }
            clause[PIVOT] = pivot; } }
    */
    if (redundancyCheck (S, clause, size, 1) == FAILED) {
      printf ("c failed at proof line %i (modulo deletion errors)\n",
              step + 1);
      return SAT;
    }
    checked++;
    S->optproof[S->nOpt++] = ad;
  }

  postprocess (S);
  return UNSAT;
}

long matchClause (struct solver *S, long *clauselist, int listsize,
                  int *input, int size) {
  int i, j;
  for (i = 0; i < listsize; ++i) {
    int *clause = S->DB + clauselist[i];
    for (j = 0; j <= size; j++)
      if (clause[j] != input[j])
        goto match_next;

    long result = clauselist[i];
    clauselist[i] = clauselist[--listsize];
    return result;
  match_next:;
  }
  return 0;
}

unsigned int getHash (int *input) {
  unsigned int sum = 0, prod = 1, xor = 0;
  while (*input) {
    prod *= *input;
    sum += *input;
    xor ^= *input;
    input++;
  }
  return (1023 * sum + prod ^ (31 * xor)) % BIGINIT;
}

int read_lit (struct solver *S, int *lit) {
  int l = 0, lc, shift = 0;
  do {
    lc = getc_unlocked (S->proofFile);
    S->nReads++;
    if ((shift == 0) && (lc == EOF))
      return EOF;
    l |= (lc & 127) << shift;
    shift += 7;
  } while (lc > 127);
  if (l % 2)
    *lit = (l >> 1) * -1;
  else
    *lit = (l >> 1);
  return 1;
}

void deactivate (struct solver *S) {
  S->nActive = 0;
  int step;
  for (step = 0; step < S->nStep; step++) {
    if ((S->proof[step] & 1) == 0) {
      int *clause = S->DB + (S->proof[step] >> INFOBITS);
      if (clause[ID] & ACTIVE)
        clause[ID] ^= ACTIVE;
    }
  }
}

void shuffleProof (struct solver *S, int iteration) {
  int i, step, _step;

  double base = 100;
  for (i = 1; i < iteration; i++)
    base *= 1.1;

  // randomly remove clause deletion steps
  for (_step = 0, step = 0; step < S->nStep; step++) {
    if (S->proof[step] & 1) {
      int length = 0;
      int *clause = S->DB + (S->proof[step] >> INFOBITS);
      while (*clause) {
        length++;
        clause++;
      }
      if ((rand () % 1000) < (base * iteration / length))
        continue;
    }
    S->proof[_step++] = S->proof[step];
  }
  S->nStep = _step;

  for (step = S->nStep - 1; step > 0; step--) {
    long a = S->proof[step];
    if (a & DBIT)
      continue;
    long b = S->proof[step - 1];
    if (b & DBIT) {
      S->proof[step] = b;
      S->proof[step - 1] = a;
    } else {
      int *c = S->DB + (a >> INFOBITS);
      int *d = S->DB + (b >> INFOBITS);
      int coinflip = 0;
      //      int coinflip = rand () / (RAND_MAX >> 1);
      if (c[MAXDEP] < d[MAXDEP] || (coinflip && (c[MAXDEP] < d[ID]))) {
        int tmp = d[ID];
        d[ID] = c[ID];
        c[ID] = tmp;
        S->proof[step] = b;
        S->proof[step - 1] = a;
      }
    }
  }

  for (step = 0; step < S->nStep; step++) {
    long ad = S->proof[step];
    if (ad & 1)
      continue;
    int *clause = S->DB + (ad >> INFOBITS);
    int i, length = 0;
    while (*clause) {
      length++;
      clause++;
    }
    clause = S->DB + (ad >> INFOBITS);
    for (i = 0; i < length - 1; i++) {
      int j = i + rand () / (RAND_MAX / (length - i) + 1);
      int t = clause[i];
      clause[i] = clause[j];
      clause[j] = t;
    }
  }
}

int parse (struct solver *S) {
  int tmp, active = 0, retvalue = SAT;
  int del = 0, fileLine = 0;
  int *buffer, bufferAlloc;

  S->nVars = 0;
  S->nClauses = 0;
  do {
    tmp = fscanf (S->inputFile, " cnf %i %li \n", &S->nVars,
                  &S->nClauses); // Read the first line
    if (tmp > 0 && tmp != EOF)
      break;
    tmp = fscanf (S->inputFile, "%*s\n");
  } // In case a comment line was found
  while (tmp != 2 && tmp != EOF); // Skip it and read next line
  int nZeros = S->nClauses;

  if (!S->nVars && !S->nClauses) {
    printf ("c ERROR: did not find p cnf line in input file\n");
    exit (0);
  }

  printf ("c parsing input formula with %i variables and %li clauses\n",
          S->nVars, S->nClauses);

  bufferAlloc = INIT;
  buffer = (int *) malloc (sizeof (int) * bufferAlloc);

  S->count = 1;
  S->nStep = 0;
  S->mem_used = 0; // The number of integers allocated in the DB

  long size;
  long DBsize = S->mem_used + BIGINIT;
  S->DB = (int *) malloc (DBsize * sizeof (int));
  if (S->DB == NULL) {
    free (buffer);
    return ERROR;
  }

  S->maxVar = 0;
  S->maxSize = 0;
  S->nLemmas = 0;
  S->nAlloc = BIGINIT;
  S->formula = (long *) malloc (sizeof (long) * S->nClauses);
  S->proof = (long *) malloc (sizeof (long) * S->nAlloc);
  long **hashTable = (long **) malloc (sizeof (long *) * BIGINIT);
  int *hashUsed = (int *) malloc (sizeof (int) * BIGINIT);
  int *hashMax = (int *) malloc (sizeof (int) * BIGINIT);

  int i;
  for (i = 0; i < BIGINIT; i++) {
    hashUsed[i] = 0;
    hashMax[i] = INIT;
    hashTable[i] = (long *) malloc (sizeof (long) * hashMax[i]);
  }

  int fileSwitchFlag = 0;
  size = 0;
  while (1) {
    int lit = 0;
    tmp = 0;
    fileSwitchFlag = nZeros <= 0;

    if (size == 0) {
      if (fileSwitchFlag) { // read for proof
        if (S->binMode) {
          int res = getc_unlocked (S->proofFile);
          if (res == EOF)
            break;
          else if (res == 97)
            del = 0;
          else if (res == 100)
            del = 1;
          else {
            printf ("c ERROR: wrong binary prefix\n");
            exit (0);
          }
          S->nReads++;
        } else {
          tmp = fscanf (S->proofFile, " d  %i ", &lit);
          if (tmp == EOF)
            break;
          del = tmp > 0;
        }
      }
    }

    if (!lit) {
      if (!fileSwitchFlag)
        tmp = fscanf (S->inputFile, " %i ", &lit); // Read a literal.
      else {
        if (S->binMode) {
          tmp = read_lit (S, &lit);
        } else {
          tmp = fscanf (S->proofFile, " %i ", &lit);
        }
      }
      if (tmp == EOF && !fileSwitchFlag) {
        if (S->warning != NOWARNING) {
          printf ("c WARNING: early EOF of the input formula\n");
          printf ("c WARNING: %i clauses less than expected\n", nZeros);
        }
        if (S->warning == HARDWARNING)
          exit (HARDWARNING);
        fileLine = 0;
        fileSwitchFlag = 1;
      }
    }

    if (tmp == 0) {
      char ignore[1024];
      if (!fileSwitchFlag) {
        if (fgets (ignore, sizeof (ignore), S->inputFile) == NULL)
          printf ("c\n");
      } else if (fgets (ignore, sizeof (ignore), S->proofFile) == NULL)
        printf ("c\n");
      for (i = 0; i < 1024; i++) {
        if (ignore[i] == '\n')
          break;
      }
      if (i == 1024) {
        printf ("c ERROR: comment longer than 1024 characters: %s\n",
                ignore);
        exit (HARDWARNING);
      }
      if (S->verb)
        printf ("c WARNING: parsing mismatch assuming a comment\n");
      continue;
    }

    if (abs (lit) > S->maxVar)
      S->maxVar = abs (lit);
    if (tmp == EOF && fileSwitchFlag)
      break;
    if (abs (lit) > S->nVars && !fileSwitchFlag) {
      printf ("c illegal literal %i due to max var %i\n", lit, S->nVars);
      exit (0);
    }
    if (!lit) {
      fileLine++;
      if (size > S->maxSize)
        S->maxSize = size;
      int pivot = buffer[0];
      buffer[size] = 0;
      qsort (buffer, size, sizeof (int), compare);
      int j = 0;
      for (i = 0; i < size; ++i) {
        if (buffer[i] == buffer[i + 1]) {
          if (S->warning != NOWARNING) {
            printf ("c WARNING: detected and deleted duplicate literal %i "
                    "at position %i of line %i\n",
                    buffer[i + 1], i + 1, fileLine);
          }
          if (S->warning == HARDWARNING)
            exit (HARDWARNING);
        } else {
          buffer[j++] = buffer[i];
        }
      }
      buffer[j] = 0;
      size = j;

      if (size == 0 && !fileSwitchFlag)
        retvalue = UNSAT;
      if (del && S->mode == BACKWARD_UNSAT && size <= 1) {
        if (S->warning != NOWARNING) {
          printf ("c WARNING: backward mode ignores deletion of (pseudo) "
                  "unit clause ");
          printClause (buffer);
        }
        if (S->warning == HARDWARNING)
          exit (HARDWARNING);
        del = 0;
        size = 0;
        continue;
      }
      int rem = buffer[0];
      buffer[size] = 0;
      unsigned int hash = getHash (buffer);
      if (del) {
        if (S->delete) {
          long match = 0;
          match = matchClause (S, hashTable[hash], hashUsed[hash], buffer,
                               size);
          if (match == 0) {
            if (S->warning != NOWARNING) {
              printf (
                  "c WARNING: deleted clause on line %i does not occur: ",
                  fileLine);
              printClause (buffer);
            }
            if (S->warning == HARDWARNING)
              exit (HARDWARNING);
            goto end_delete;
          }
          if (S->mode == FORWARD_SAT)
            S->DB[match - 2] = rem;
          hashUsed[hash]--;
          active--;
          if (S->nStep == S->nAlloc) {
            S->nAlloc = (S->nAlloc * 3) >> 1;
            S->proof =
                (long *) realloc (S->proof, sizeof (long) * S->nAlloc);
            //              printf ("c proof allocation increased to %li\n",
            //              S->nAlloc);
            if (S->proof == NULL) {
              printf ("c MEMOUT: reallocation of proof list failed\n");
              exit (0);
            }
          }
          S->proof[S->nStep++] = (match << INFOBITS) + 1;
        }
      end_delete:;
        if (del) {
          del = 0;
          size = 0;
          continue;
        }
      }

      if (S->mem_used + size + EXTRA > DBsize) {
        DBsize = (DBsize * 3) >> 1;
        S->DB = (int *) realloc (S->DB, DBsize * sizeof (int));
        //        printf("c database increased to %li\n", DBsize);
        if (S->DB == NULL) {
          printf ("c MEMOUT: reallocation of clause database failed\n");
          exit (0);
        }
      }
      int *clause = &S->DB[S->mem_used + EXTRA - 1];
      if (size != 0)
        clause[PIVOT] = pivot;
      clause[ID] = 2 * S->count;
      S->count++;
      if (S->mode == FORWARD_SAT)
        if (nZeros > 0)
          clause[ID] |= ACTIVE;

      for (i = 0; i < size; ++i) {
        clause[i] = buffer[i];
      }
      clause[i] = 0;
      S->mem_used += size + EXTRA;

      hash = getHash (clause);
      if (hashUsed[hash] == hashMax[hash]) {
        hashMax[hash] = (hashMax[hash] * 3) >> 1;
        hashTable[hash] = (long *) realloc (
            hashTable[hash], sizeof (long *) * hashMax[hash]);
        if (hashTable[hash] == NULL) {
          printf ("c MEMOUT reallocation of hash table %i failed\n", hash);
          exit (0);
        }
      }
      hashTable[hash][hashUsed[hash]++] = (long) (clause - S->DB);

      active++;
      if (nZeros > 0) { // if still parsing the formula
        S->formula[S->nClauses - nZeros] =
            (((long) (clause - S->DB)) << INFOBITS);
      } else {
        if (S->nStep == S->nAlloc) {
          S->nAlloc = (S->nAlloc * 3) >> 1;
          S->proof = (long *) realloc (S->proof, sizeof (long) * S->nAlloc);
          //        printf ("c proof allocation increased to %li\n",
          //        S->nAlloc);
          if (S->proof == NULL) {
            printf ("c MEMOUT: reallocation of proof list failed\n");
            exit (0);
          }
        }
        S->proof[S->nStep++] = (((long) (clause - S->DB)) << INFOBITS);
      }

      if (nZeros <= 0)
        S->nLemmas++;

      if (!nZeros)
        S->lemmas =
            (long) (clause - S->DB); // S->lemmas is no longer pointer
      size = 0;
      del = 0;
      --nZeros;
    } // Reset buffer
    else {
      buffer[size++] = lit; // Add literal to buffer
      if (size == bufferAlloc) {
        bufferAlloc = (bufferAlloc * 3) >> 1;
        buffer = (int *) realloc (buffer, sizeof (int) * bufferAlloc);
      }
    }
  }

  if (S->mode == FORWARD_SAT && active) {
    if (S->warning != NOWARNING)
      printf ("c WARNING: %i clauses active if proof succeeds\n", active);
    if (S->warning == HARDWARNING)
      exit (HARDWARNING);
    for (i = 0; i < BIGINIT; i++) {
      int j;
      for (j = 0; j < hashUsed[i]; j++) {
        printf ("c ");
        int *clause = S->DB + hashTable[i][j];
        printClause (clause);
        if (S->nStep == S->nAlloc) {
          S->nAlloc = (S->nAlloc * 3) >> 1;
          S->proof = (long *) realloc (S->proof, sizeof (long) * S->nAlloc);
          //          printf ("c proof allocation increased to %li\n",
          //          S->nAlloc);
          if (S->proof == NULL) {
            printf ("c MEMOUT: reallocation of proof list failed\n");
            exit (0);
          }
        }
        S->proof[S->nStep++] = (((int) (clause - S->DB)) << INFOBITS) + 1;
      }
    }
  }

  S->DB = (int *) realloc (S->DB, S->mem_used * sizeof (int));

  for (i = 0; i < BIGINIT; i++)
    free (hashTable[i]);
  free (hashTable);
  free (hashUsed);
  free (hashMax);
  free (buffer);

  printf ("c finished parsing");
  if (S->nReads)
    printf (", read %li bytes from proof file", S->nReads);
  printf ("\n");

  int n = S->maxVar;
  S->falseStack = (int *) malloc (
      (n + 1) * sizeof (int)); // Stack of falsified literals -- this
                               // pointer is never changed
  S->reason = (long *) malloc ((n + 1) * sizeof (long)); // Array of clauses
  S->used = (int *) malloc ((2 * n + 1) * sizeof (int));
  S->used += n; // Labels for variables, non-zero means false
  S->max = (int *) malloc ((2 * n + 1) * sizeof (int));
  S->max += n; // Labels for variables, non-zero means false
  S->falseA = (int *) malloc ((2 * n + 1) * sizeof (int));
  S->falseA += n; // Labels for variables, non-zero means false
  S->setMap = (int *) malloc ((2 * n + 1) * sizeof (int));
  S->setMap += n; // Labels for variables, non-zero means false
  S->setTruth = (int *) malloc ((2 * n + 1) * sizeof (int));
  S->setTruth += n; // Labels for variables, non-zero means false

  S->optproof =
      (long *) malloc (sizeof (long) * (2 * S->nLemmas + S->nClauses));

  S->maxRAT = INIT;
  S->RATset = (int *) malloc (sizeof (int) * S->maxRAT);
  for (i = 0; i < S->maxRAT; i++)
    S->RATset[i] = 0; // is this required?

  S->preRAT = (int *) malloc (sizeof (int) * n);

  S->lratAlloc = INIT;
  S->lratSize = 0;
  S->lratTable = (int *) malloc (sizeof (int) * S->lratAlloc);
  S->lratLookup = (long *) malloc (sizeof (long) * (S->count + 1));

  S->maxDependencies = INIT;
  S->dependencies = (int *) malloc (sizeof (int) * S->maxDependencies);
  for (i = 0; i < S->maxDependencies; i++)
    S->dependencies[i] = 0; // is this required?

  S->wlist = (long **) malloc (sizeof (long *) * (2 * n + 1));
  S->wlist += n;

  for (i = 1; i <= n; ++i) {
    S->max[i] = S->max[-i] = INIT;
    S->setMap[i] = S->setMap[-i] = 0;
    S->setTruth[i] = S->setTruth[-i] = 0;
    S->wlist[i] = (long *) malloc (sizeof (long) * S->max[i]);
    S->wlist[-i] = (long *) malloc (sizeof (long) * S->max[-i]);
  }

  S->unitStack = (long *) malloc (sizeof (long) * n);

  return retvalue;
}

void freeMemory (struct solver *S) {
  int i;
  //  printf("c database size %li; ", S->mem_used);
  //  int sum = 0;
  //  for (i = 1; i <= S->maxVar; i++)
  //    sum += S->max[i] + S->max[-i];
  //  printf(" watch pointers size %i.\n", sum);

  free (S->DB);
  free (S->falseStack);
  free (S->reason);
  free (S->proof);
  free (S->formula);
  for (i = 1; i <= S->maxVar; ++i) {
    free (S->wlist[i]);
    free (S->wlist[-i]);
  }
  free (S->used - S->maxVar);
  free (S->max - S->maxVar);
  free (S->falseA - S->maxVar);
  free (S->wlist - S->maxVar);
  free (S->RATset);
  free (S->dependencies);
  return;
}

int onlyDelete (struct solver *S, int begin, int end) {
  int step;
  for (step = begin; step < end; step++)
    if ((S->proof[step] & 1) == 0)
      return 0;
  return 1;
}

void printHelp () {
  printf ("usage: drat-trim [INPUT] [<PROOF>] [<option> ...]\n\n");
  printf ("where <option> is one of the following\n\n");
  printf ("  -h          print this command line option summary\n");
  printf ("  -c CORE     prints the unsatisfiable core to the file CORE "
          "(DIMACS format)\n");
  printf ("  -a ACTIVE   prints the active clauses to the file ACTIVE "
          "(DIMACS format)\n");
  printf ("  -l LEMMAS   prints the core lemmas to the file LEMMAS (DRAT "
          "format)\n");
  printf ("  -L LEMMAS   prints the core lemmas to the file LEMMAS (LRAT "
          "format)\n");
  printf ("  -r TRACE    resolution graph in the TRACE file (TRACECHECK "
          "format)\n\n");
  printf ("  -t <lim>    time limit in seconds (default %i)\n", TIMEOUT);
  printf ("  -u          default unit propagation (i.e., no core-first)\n");
  printf ("  -f          forward mode for UNSAT\n");
  printf ("  -v          more verbose output\n");
  printf ("  -b          show progress bar\n");
  printf ("  -O          optimize proof till fixpoint by repeating "
          "verification\n");
  printf ("  -C          compress core lemmas (emit binary proof)\n");
  printf ("  -D          delete proof file after parsing\n");
  printf ("  -w          suppress warning messages\n");
  printf ("  -W          exit after first warning\n");
  printf ("  -p          run in plain mode (i.e., ignore deletion "
          "information)\n\n");
  printf ("  -R          turn off reduce mode\n\n");
  printf ("  -S          run in SAT check mode (forward checking)\n\n");
  printf ("and input and proof are specified as follows\n\n");
  printf ("  INPUT       input file in DIMACS format\n");
  printf (
      "  PROOF       proof file in DRAT format (stdin if no argument)\n\n");
  exit (0);
}

int main (int argc, char **argv) {
  struct solver S;

  S.inputFile = NULL;
  S.proofFile = stdin;
  S.coreStr = NULL;
  S.activeFile = NULL;
  S.lemmaStr = NULL;
  S.lratFile = NULL;
  S.traceFile = NULL;
  S.timeout = TIMEOUT;
  S.nReads = 0;
  S.nWrites = 0;
  S.mask = 0;
  S.verb = 0;
  S.delProof = 0;
  S.backforce = 0;
  S.optimize = 0;
  S.warning = 0;
  S.prep = 0;
  S.bar = 0;
  S.mode = BACKWARD_UNSAT;
  S.delete = 1;
  S.reduce = 1;
  S.binMode = 0;
  S.binOutput = 0;
  gettimeofday (&S.start_time, NULL);

  int i, tmp = 0;
  for (i = 1; i < argc; i++) {
    if (argv[i][0] == '-') {
      if (argv[i][1] == 'h')
        printHelp ();
      else if (argv[i][1] == 'c')
        S.coreStr = argv[++i];
      else if (argv[i][1] == 'a')
        S.activeFile = fopen (argv[++i], "w");
      else if (argv[i][1] == 'l')
        S.lemmaStr = argv[++i];
      else if (argv[i][1] == 'L')
        S.lratFile = fopen (argv[++i], "w");
      else if (argv[i][1] == 'r')
        S.traceFile = fopen (argv[++i], "w");
      else if (argv[i][1] == 't')
        S.timeout = atoi (argv[++i]);
      else if (argv[i][1] == 'b')
        S.bar = 1;
      else if (argv[i][1] == 'B')
        S.backforce = 1;
      else if (argv[i][1] == 'O')
        S.optimize = 1;
      else if (argv[i][1] == 'C')
        S.binOutput = 1;
      else if (argv[i][1] == 'D')
        S.delProof = 1;
      else if (argv[i][1] == 'u')
        S.mask = 1;
      else if (argv[i][1] == 'v')
        S.verb = 1;
      else if (argv[i][1] == 'w')
        S.warning = NOWARNING;
      else if (argv[i][1] == 'W')
        S.warning = HARDWARNING;
      else if (argv[i][1] == 'p')
        S.delete = 0;
      else if (argv[i][1] == 'R')
        S.reduce = 0;
      else if (argv[i][1] == 'f')
        S.mode = FORWARD_UNSAT;
      else if (argv[i][1] == 'S')
        S.mode = FORWARD_SAT;
    } else {
      tmp++;
      if (tmp == 1) {
        S.inputFile = fopen (argv[1], "r");
        if (S.inputFile == NULL) {
          printf ("c error opening \"%s\".\n", argv[i]);
          return ERROR;
        }
      }

      else if (tmp == 2) {
        S.proofFile = fopen (argv[2], "r");
        if (S.proofFile == NULL) {
          printf ("c error opening \"%s\".\n", argv[i]);
          return ERROR;
        }

        int j;
        for (j = 0; j < 10; j++) {
          int c = getc_unlocked (S.proofFile);
          if (c == EOF)
            break;
          if ((c != 100) && (c != 10) && (c != 13) && (c != 32) &&
              (c != 45) && ((c < 48) || (c > 57)) &&
              ((c < 65) || (c > 122))) {
            printf ("c turning on binary mode checking\n");
            S.binMode = 1;
            break;
          }
        }
        fclose (S.proofFile);
        S.proofFile = fopen (argv[2], "r");
        if (S.proofFile == NULL) {
          printf ("c error opening \"%s\".\n", argv[i]);
          return ERROR;
        }
      }
    }
  }

  if (tmp == 1)
    printf ("c reading proof from stdin\n");
  if (tmp == 0)
    printHelp ();

  int parseReturnValue = parse (&S);

  fclose (S.inputFile);
  fclose (S.proofFile);

  if (S.mode == FORWARD_UNSAT) {
    S.reduce = 0;
  }

  if (S.delProof && argv[2] != NULL) {
    int ret = remove (argv[2]);
    if (ret == 0)
      printf ("c deleted proof %s\n", argv[2]);
  }

  int sts = ERROR;
  if (parseReturnValue == ERROR)
    printf ("s MEMORY ALLOCATION ERROR\n");
  else if (parseReturnValue == UNSAT)
    printf ("c trivial UNSAT\ns VERIFIED\n"), sts = UNSAT;
  else if ((sts = verify (&S, -1, -1)) == UNSAT)
    printf ("s VERIFIED\n");
  else
    printf ("s NOT VERIFIED\n");
  struct timeval current_time;
  gettimeofday (&current_time, NULL);
  long runtime = (current_time.tv_sec - S.start_time.tv_sec) * 1000000 +
                 (current_time.tv_usec - S.start_time.tv_usec);
  printf ("c verification time: %.3f seconds\n",
          (double) (runtime / 1000000.0));

  if (S.optimize) {
    printf ("c proof optimization started (ignoring the timeout)\n");
    int iteration = 1;
    //    while (iteration < 20) {
    while (S.nRemoved) {
      deactivate (&S);
      shuffleProof (&S, iteration);
      iteration++;
      verify (&S, 0, 0);
    }
  }

  freeMemory (&S);
  return (sts != UNSAT); // 0 on success, 1 on any failure
}
