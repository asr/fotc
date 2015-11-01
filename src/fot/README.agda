------------------------------------------------------------------------------
-- FOT (First-Order Theories)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Code accompanying the PhD thesis "Reasoning about Functional
-- Programs by Combining Interactive and Automatic Proofs" by Andrés
-- Sicard-Ramírez.

-- The code presented here does not match the thesis exactly.

module README where

------------------------------------------------------------------------------
-- Description

-- Examples of the formalization of first-order theories showing the
-- combination of interactive proofs with automatics proofs carried
-- out by first-order automatic theorem provers (ATPs).

------------------------------------------------------------------------------
-- For the thesis, prerequisites, tested versions of the ATPs and use,
-- see https://github.com/asr/fotc/.

------------------------------------------------------------------------------
-- Conventions

-- If the module's name ends in 'I' the module contains interactive
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
