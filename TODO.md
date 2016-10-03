# TODO

As the goal for this solver is to produce a simplified easy to change CDCL
solver, there are two types of TODO's here.

## Simplifications

First we list things to simplify or to remove.

Some of them first need proper benchmarking to avoid oversimplifying the solver:

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


Mo 3. Okt 07:26:33 PDT 2016
