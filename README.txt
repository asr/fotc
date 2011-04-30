==============================================================================
agda2atp
==============================================================================

Code accompanying the paper "Combining Interactive and Automatic
Theorem Proving for Reasoning about Functional Programs" by Ana Bove,
Peter Dybjer, and Andrés Sicard-Ramírez.

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

* Vampire (http://www.vprover.org/)

------------------------------------------------------------------------------
Installation
------------------------------------------------------------------------------

1. Prerequisite: A modified version of Agda

  The agda2atp tool requires a modified version of Agda in which have
  added a new built-in pragma called the ATP pragma. To install this
  modified version of Agda you need:

  1.1 Getting the modified version of Agda source

      $ darcs get http://patch-tag.com/r/asr/magda

  1.2 To install the modified version of Agda Agda

      You can following the same instructions to install Agda from the
      Agda wiki http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.Download.

      N.B. In our modified version of Agda we bump the Agda
      development version of from 2.2.9 to 2.2.9.1.

2. Getting the agda2atp source

   $ darcs get http://patch-tag.com/r/asr/agda2atp

3. To install the agda2atp tool

   After to install the modified version of Agda, you need:

   $ cd ~/agda2atp
   $ cabal install

4. Testing

   In the file ~/agda2atp/Makefile set the AGDA2APT variable to the
   ATP of your choice. For example, if you choose the Metis ATP, you
   should set the variable AGDA2APT to

   AGDA2ATP = agda2atp --atp=metis

   To test the correct installation of the agda2apt tool you need:

   $ make test

   After this command you should be see the following output

   Translating Test/Succeed/Agda/InterfaceFile.agda ...
   Translating Test/Succeed/Conjectures/Eta.agda ...
   Proving the conjecture in /tmp/Test.Succeed.Conjectures.Eta.test1_18.tptp ...
   Metis proved the conjecture in /tmp/Test.Succeed.Conjectures.Eta.test1_18.tptp
   ...
   Proving the conjecture in /tmp/Test.Fail.Add.43-comm_19.tptp ...
   The ATP(s) ["metis"] did not prove the conjecture in /tmp/Test.Fail.Add.43-comm_19.tptp

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

4. Vampire executable

The vampire executable name is based on the architecture
(e.g. vampire_lin32, vampire_lin64, vampire_mac, and vampire_win.exe),
therefore the agda2atp tool expects the generic name "vampire".

------------------------------------------------------------------------------
Bug report
------------------------------------------------------------------------------

Please send your bug reports to andres.sicard.ramirez@gmail.com.
