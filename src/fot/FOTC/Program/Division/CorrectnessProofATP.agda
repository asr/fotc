------------------------------------------------------------------------------
-- The division program is correct
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

-- This module proves the correctness of the division program using
-- repeated subtraction (Dybjer 1985).

module FOTC.Program.Division.CorrectnessProofATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP

import FOTC.Data.Nat.Induction.NonAcc.WF-ATP
open module WFInd = FOTC.Data.Nat.Induction.NonAcc.WF-ATP.WFInd

open import FOTC.Program.Division.Division
open import FOTC.Program.Division.ResultATP
open import FOTC.Program.Division.Specification
open import FOTC.Program.Division.TotalityATP

------------------------------------------------------------------------------
-- The division program is correct when the dividend is less than the
-- divisor.
div-x<y-correct : ∀ {i j} → N i → N j → i < j → divSpec i j (div i j)
div-x<y-correct Ni Nj i<j = div-x<y-N i<j , div-x<y-resultCorrect Ni Nj i<j

-- The division program is correct dividend is greater or equal than
-- the divisor.
div-x≮y-correct : ∀ {i j} → N i → N j →
                 (∀ {i'} → N i' → i' < i → divSpec i' j (div i' j)) →
                 j > zero →
                 i ≮ j →
                 divSpec i j (div i j)
div-x≮y-correct {i} {j} Ni Nj ah j>0 i≮j =
  div-x≮y-N ih i≮j , div-x≮y-resultCorrect Ni Nj ih i≮j

  where
  -- The inductive hypothesis on i ∸ j.
  ih : divSpec (i ∸ j) j (div (i ∸ j) j)
  ih = ah {i ∸ j}
          (∸-N Ni Nj)
          (x≥y→y>0→x∸y<x Ni Nj (x≮y→x≥y Ni Nj i≮j) j>0)

------------------------------------------------------------------------------
-- The division program is correct.

-- We do the well-founded induction on i and we keep j fixed.
divCorrect : ∀ {i j} → N i → N j → j > zero → divSpec i j (div i j)
divCorrect {j = j} Ni Nj j>0 = <-wfind A ih Ni
  where
  A : D → Set
  A d = divSpec d j (div d j)

  -- The inductive step doesn't use the variable i (nor Ni). To make
  -- this clear we write down the inductive step using the variables m
  -- and n.
  ih : ∀ {n} → N n → (∀ {m} → N m → m < n → A m) → A n
  ih {n} Nn ah =
    case (div-x<y-correct Nn Nj) (div-x≮y-correct Nn Nj ah j>0) (x<y∨x≮y Nn Nj)

------------------------------------------------------------------------------
-- References:
--
-- • Dybjer, Peter (1985). Program Veriﬁcation in a Logical Theory of
--   Constructions. In: Functional Programming Languages and Computer
--   Architecture. Ed. by Jouannaud,
--   Jean-Pierre. Vol. 201. LNCS. Appears in revised form as
--   Programming Methodology Group Report 26, University of Gothenburg
--   and Chalmers University of Technology, June 1986. Springer,
--   pp. 334–349.
