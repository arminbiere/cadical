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

  - Propagation speed goes down if we do not use 'blocking' literal.  The
    same applies if 'binary' and 'large' clauses are merged.  Still after
    we got to fix-point we should revisit these design decisions.

  - Check whether the complicated EMA initialization is necessary.

## Additions

Second things are listed related to additional features.
  
  - Binary DRAT proof trace format.

  - Add bounded variable elimination and blocked clause elimination.

  - Subsumption of learned clauses as in Splatz.

  - Equivalent literal substitution.

## General

There should be an ongoing process of refactoring and documenting the code
and in particular remove part of the code which is not used anymore.


Do 29. Sep 23:47:17 CEST 2016
