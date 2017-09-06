# declarative-semantics

miniKanren prototype of ['Declarative semantics for functional languages: compositional, extensional, and elementary'](https://arxiv.org/abs/1707.03762) by Jeremy Siek.

Code written by Ramana Kumar and Will Byrd, after discussion with Jeremy Siek.

The code implements the interesting parts of Figure 2 on page 7 of the paper.

There are currently two versions of the code:

* tables-subsets.scm, which is the closer of the two implementations to the spirit of Figure 2.  The Subset relation is explicit.

* tables.scm, in which the subset relation is implicit.

tables-subsets.scm seems to be closer to the spirit of Figure 2.

Questions/Future Work:

* Are the two implementations equivalent?

* Is there a way to avoid generating "duplicate" tables, perhaps through tabling or through laziness/new constraints?

* Implement the rest of the paper.

* Explore how well this version of the relational interpreter works for problems we care about (quines, recursive program synthesis, etc.).