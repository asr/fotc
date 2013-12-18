------------------------------------------------------------------------------
-- FOT (First-Order Theories)
------------------------------------------------------------------------------

-- Code accompanying the paper Combining Interactive and Automatic
-- Reasoning in First Order Theories of Functional Programs by Ana
-- Bove, Peter Dybjer and Andrés Sicard-Ramírez (FoSSaCS 2012).

-- The code presented here does not match the paper exactly.

module README where

------------------------------------------------------------------------------
-- Description

-- Examples of the formalization of first-order theories showing the
-- combination of interactive proofs with automatics proofs carried
-- out by first-order automatic theorem provers (ATPs).

------------------------------------------------------------------------------
-- Paper, prerequisites, tested versions of the ATPS and use

-- See https://github.com/asr/fotc/.

------------------------------------------------------------------------------
-- Conventions

-- In the modules with the formalization of the first-order theories,
-- if the module's name ends in 'I' the module contains interactive
-- proofs, if it ends in 'ATP' the module contains combined proofs,
-- otherwise the module contains definitions and/or interactive proofs
-- that are used by the interactive and combined proofs.

------------------------------------------------------------------------------
-- First-order theories
------------------------------------------------------------------------------

-- • First-order logic with equality

-- First-order logic (FOL)
open import FOL.README

-- Propositional equality
open import Common.FOL.Relation.Binary.PropositionalEquality

-- Equality reasoning
open import Common.FOL.Relation.Binary.EqReasoning

-- • Group theory

open import GroupTheory.README

-- • Distributive laws on a binary operation (Stanovský example)

open import DistributiveLaws.README

-- • First-order Peano arithmetic (PA)

open import PA.README

-- • First-Order Theory of Combinators (FOTC)

open import FOTC.README

-- • Logical Theory of Constructions for PCF (LTC-PCF)

open import LTC-PCF.README

------------------------------------------------------------------------------
-- Agsy examples
------------------------------------------------------------------------------

-- We cannot import the Agsy examples because some modules contain
-- unsolved metas, therefore see examples/Agsy/README.txt
