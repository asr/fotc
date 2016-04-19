Agda formalisation of FOTC (First-Order Theory of Combinators)
==============================================================

Description
-----------

[Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php) formalisation
of FOTC (First-Order Theory of Combinators) which is a programming
logic for functional programs that can deal with *general recursion*,
*higher-order functions*, *termination proofs*, *partial functions*,
and *inductive* and *co-inductive* predicates. Our implementation
includes a translation of Agda representations of formulae in FOTC
into the [TPTP](http://www.cs.miami.edu/~tptp/) language, which is a
standard format for input and output in automatic theorem provers
(ATPs), so that we can call off-the-shelf ATPs when proving properties
of our programs. For this purpose we wrote the
[Apia](https://github.com/asr/apia) program.

Related publications
--------------

* [Andrés Sicard-Ramírez](http://www1.eafit.edu.co/asr/)
  (2015). [Reasoning about Functional Programs by Combining Interactive and Automatic Proofs](http://www1.eafit.edu.co/asr/publications.html#phd-thesis)
  (PhD thesis).

* [Ana Bove](http://www.cse.chalmers.se/~bove/),
  [Peter Dybjer](http://www.cse.chalmers.se/~peterd/) and
  [Andrés Sicard-Ramírez](http://www1.eafit.edu.co/asr/). [Combining Interactive and Automatic Reasoning in First Order Theories of Functional Programs](http://www1.eafit.edu.co/asr/publications.html#fossacs-2012)
  (FoSSaCS 2012).

* [Ana Bove](http://www.cse.chalmers.se/~bove/),
  [Peter Dybjer](http://www.cse.chalmers.se/~peterd/) and
  [Andrés Sicard-Ramírez](http://www1.eafit.edu.co/asr/). [Embedding a Logical Theory of Constructions in Agda](http://www1.eafit.edu.co/asr/publications.html#plpv-2009)
  (PLPV'09).

Prerequisites and use
---------------------

* The [Apia](https://github.com/asr/apia/blob/master/README.md) program

* Setting up the Emacs mode for use with our library of first-order
   theories

   It is necessary to add the path `fotc/src/fot`.

Examples in our FoSSaCS-2012 paper
----------------------------------

Please note that the code presented here does not match the paper
exactly.

You can follow these links to see the examples shown in our
[FoSSaCS-2012 paper](http://www1.eafit.edu.co/asr/publications.html#fossacs-2012):

* [The McCarthy's 91-function example](http://asr.github.io/fotc/FOTC.Program.McCarthy91.PropertiesATP.html)

* [The mirror function example](http://asr.github.io/fotc/FOTC.Program.Mirror.PropertiesATP.html)

* [The alternating bit protocol example](http://asr.github.io/fotc/FOTC.Program.ABP.CorrectnessProofATP.html)

You can test for example the proofs regarding the mirror function with
the following commands:

````bash
$ cd fotc/src/fot
$ agda FOTC/Program/Mirror/PropertiesATP.agda
$ apia FOTC/Program/Mirror/PropertiesATP.agda
````

Examples in our PLPV-2009 paper
-------------------------------

Please note that the code presented here does not match the paper
exactly. Also note that the code below does not require neither the
version modified of Agda nor the Apia program.

You can follow
[this link](http://asr.github.io/fotc/LTC-PCF.README.html) to see the
examples shown in our
[PLPV-2009 paper](http://www1.eafit.edu.co/asr/publications.html#plpv-2009).

You can test for example the verification of the GCD algorithm with
the following commands:

````bash
$ cd fotc/src/fot
$ agda LTC-PCF/Program/GCD/Partial/ProofSpecification.agda
````

More examples
-------------

We also have more examples related with first-order theories like
group theory or Peano arithmetic. In addition there are more examples
related to the verification of functional programs. You can browse all
the examples from the file
[README.html](http://asr.github.io/fotc/README.html).

Tested with
-----------
The files in this repository have been tested with:

Agda files: Development versions of
[Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php), the Agda
[standard library](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary),
the [extended](https://github.com/asr/eagda/blob/master/README.md)
version of Agda and/or
[Apia](https://github.com/asr/apia/blob/master/README.md)
corresponding to the date of the last commit.

Coq files: [Coq](https://coq.inria.fr/) 8.5pl1.

Haskell files: [GHC](https://www.haskell.org/ghc/) 7.10.3
