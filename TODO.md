# TODO

As the goal for this solver is to produce a simplified easy to change CDCL
solver, there are two types of TODO's here.

## Simplifications

First we list things to simplify or to remove.

Some of them first need proper benchmarking to avoid oversimplifying the solver:

  - Check if a reentrant, e.g., non static version is slower, and if not add
    everything to a 'CaDiCaL' class.

  - It seems that some people think putting everything in one file is bad
    resutling in the source code to be hard to follow, navigate and
    understand.  To serve those users we can put common stuff into separate
    files (this is related to the first point above).

  - The recursive minimization seems even faster than the non-recursive
    version and thus we should remove the code for the non-recursive version
    (at one-point).

  - Propagation speed goes down if we do not use 'blocking' literal.  The
    same applies if 'binary' and 'large' clauses are merged.  Still after
    we got to fix-point we should revisit these design decisions.

  - Remove some redundant code related to disabled options.

  - Maybe remove the C++ operator hacks, to make the code easier to
    understand.

  - Check whether the complicated EMA initialization is necessary.

## Additions

Second things are listed related to additional features.
  
  - Complete the arena allocation of large clauses and use 32-bit clause
    references.  This is probably a bigger deal.

  - Try a moving cache access optimizing garbage collector, which gave
    for Splatz 15% after the arena based allocator works.

  - Binary DRAT proof trace format.

  - Add bounded variable elimination and blocked clause elimination.

  - Subsumption of learned clauses as in Splatz.

  - Equivalent literal substitution.

## General

There should be an ongoing process of refactoring and documenting the code.


Fr 9. Sep 15:21:44 CEST 2016
