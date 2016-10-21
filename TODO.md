# TODO

As the goal for this solver is to produce a simplified easy to understand, easy to
change, and easy to analyze CDCL solver, there are two types of TODO's here.

## Simplifications

First we list things to simplify or to remove.

Some of them first need proper benchmarking to avoid oversimplifying the solver:

  - Check whether the complicated EMA initialization is necessary.

  - Check that to propagating after binary conflicts really gives a benefit.

## Additions

Second things are listed related to additional features.
  
  - Add bounded variable elimination and blocked clause elimination.

  - Subsumption of learned clauses as in Splatz.

  - Equivalent literal substitution.

## General

There should be an ongoing process of refactoring and documenting the code
and in particular remove part of the code which is not used anymore.

Fr 21. Okt 21:16:09 CEST 2016
