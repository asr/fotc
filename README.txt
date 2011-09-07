==============================================================================
agda2atp
==============================================================================

Code accompanying the paper "Combining Interactive and Automatic
Reasoning about Functional Programs" by Ana Bove, Peter Dybjer, and
Andrés Sicard-Ramírez.

------------------------------------------------------------------------------
Description
------------------------------------------------------------------------------

The agda2atp tool is a program for proving first order formulae
written in the dependently typed language Agda using first order
automatic theorem provers (ATPs), via the translation of the Agda
formulae to the TPTP format which is a standard for input and output
for the ATPs.

------------------------------------------------------------------------------
Prerequisites
------------------------------------------------------------------------------

The agda2atp tool requires at least one of the following ATPs:

* E (http://www4.informatik.tu-muenchen.de/~schulz/WORK/eprover.html)

* Equinox (http://www.cse.chalmers.se/~koen/code/)

* Metis (http://www.gilith.com/software/metis/)

* SPASS (http://www.spass-prover.org/)

* Vampire (http://www.vprover.org/)

------------------------------------------------------------------------------
Installation
------------------------------------------------------------------------------

See http://www1.eafit.edu.co/asicard/code/fotc/.

------------------------------------------------------------------------------
Known bugs and/or limitations
------------------------------------------------------------------------------

1. Logical symbols

The following symbols are hard-coded, i.e. they should be used

false                  : ⊥
true                   : ⊤
negation               : ¬_
conjunction            : _∧_
disjunction            : _∨_
implication            : _⇒_ or the Agda functional space
equivalence            : _↔_
universal quantifier   : ⋀ or the Agda functional space
existential quantifier : ∃
equality               : _≡_

2. Agda version

The agda2atp tool must be compiled using the same version of Agda that
is used to generate the Agda interface files.

3. Place of the ATP pragmas

The ATP pragmas should be declared in the same module that the Agda
entity (type, definition, data constructor) which it refers.

------------------------------------------------------------------------------
Bug report
------------------------------------------------------------------------------

Please send your bug reports to andres.sicard.ramirez@gmail.com.
