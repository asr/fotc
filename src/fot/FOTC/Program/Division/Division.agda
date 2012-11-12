------------------------------------------------------------------------------
-- Division program
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module define a division program using repeated subtraction
-- (Dybjer 1985).

-- Peter Dybjer. Program verification in a logical theory of
-- constructions. In Jean-Pierre Jouannaud, editor. Functional
-- Programming Languages and Computer Architecture, volume 201 of
-- LNCS, 1985, pages 334-349. Appears in revised form as Programming
-- Methodology Group Report 26, June 1986.

module FOTC.Program.Division.Division where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------

postulate
  div    : D → D → D
  div-eq : ∀ i j → div i j ≡ if (lt i j) then zero else succ₁ (div (i ∸ j) j)
{-# ATP axiom div-eq #-}
