Description
-----------

`agda2atp` is a Haskell program for proving first-order formulae
written in [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php)
using first-order automatic theorem provers (ATPs). Before calling the
ATPs, the Agda formulae are translated into
[TPTP](http://www.cs.miami.edu/~tptp/) format, which is a standard
format for input and output in ATPs.

The program `agda2atp` is part of the code accompanying the paper
  [Combining Interactive and Automatic Reasoning in First Order
  Theories of Functional
  Programs](http://www1.eafit.edu.co/asicard/publications-talks/proceedings_abstracts.html#Bove-Dybjer-SicardRamirez-2012)
  by [Ana Bove](http://www.cse.chalmers.se/~bove/), [Peter
  Dybjer](http://www.cse.chalmers.se/~peterd/), and [Andrés
  Sicard-Ramírez] (http://www1.eafit.edu.co/asicard/)</a> (FoSSaCS
  2012).

Prerequisites
-------------

The program `agda2atp` requires at least one of the following ATPs:
[E](http://www4.informatik.tu-muenchen.de/~schulz/WORK/eprover.html),
[Equinox](http://www.cse.chalmers.se/~koen/code/),
[Metis](http://www.gilith.com/software/metis/),
[SPASS](http://www.spass-prover.org/), or
[Vampire](http://www.vprover.org/).

Installation
------------

See http://www1.eafit.edu.co/asicard/code/fossacs-2012/index.html.

Known bugs and/or limitations
-----------------------------

* Logical symbols

The following symbols are hard-coded, i.e. they should be used: `⊥`
(false), `⊤` (true), `¬_` (negation), `_∧_` (conjunction), `_∨_`
(disjunction), the Agda non-dependent function type `→` (implication),
`_↔_` (equivalence), the Agda dependent function type `(x : A) → B`
(universal quantifier), `∃` (existential quantifier), and `_≡_`
(propositional equality).

* Agda version

The program `agda2atp` must be compiled using the same version of Agda that
was used to generate the Agda interface files.

* Place of the ATP pragmas

The ATP pragmas should be declared in the same module that the Agda
entity (type, definition, data constructor) which it refers.
