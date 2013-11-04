------------------------------------------------------------------------------
-- The division program satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the division program using
-- repeated subtraction (Dybjer 1985).

-- References:
--
-- • Dybjer, Peter (1985). Program Veriﬁcation in a Logical Theory of
--   Constructions. In: Functional Programming Languages and Computer
--   Architecture. Ed. by Jouannaud,
--   Jean-Pierre. Vol. 201. LNCS. Appears in revised form as
--   Programming Methodology Group Report 26, University of Gothenburg
--   and Chalmers University of Technology, June 1986. Springer,
--   pp. 334–349.

module FOTC.Program.Division.SpecificationProofI where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI

import FOTC.Data.Nat.Induction.NonAcc.WF-I
open module WFInd = FOTC.Data.Nat.Induction.NonAcc.WF-I.WFInd

open import FOTC.Program.Division.Division
open import FOTC.Program.Division.IsCorrectI
open import FOTC.Program.Division.Specification
open import FOTC.Program.Division.TotalityI

------------------------------------------------------------------------------
-- The division result satifies the specification DIV
-- when the dividend is less than the divisor.
div-x<y-DIV : ∀ {i j} → N i → N j → i < j → DIV i j (div i j)
div-x<y-DIV Ni Nj i<j = div-x<y-N i<j , div-x<y-correct Ni Nj i<j

-- The division result satisfies the specification DIV when the
-- dividend is greater or equal than the divisor.
div-x≮y-DIV : ∀ {i j} → N i → N j →
              (∀ {i'} → N i' → i' < i → DIV i' j (div i' j)) →
              j > zero →
              i ≮ j →
              DIV i j (div i j)
div-x≮y-DIV {i} {j} Ni Nj ah j>0 i≮j =
  div-x≮y-N ih i≮j , div-x≮y-correct Ni Nj ih i≮j

  where
  -- The inductive hypothesis on i ∸ j.
  ih : DIV (i ∸ j) j (div (i ∸ j) j)
  ih = ah {i ∸ j}
          (∸-N Ni Nj)
          (x≥y→y>0→x∸y<x Ni Nj (x≮y→x≥y Ni Nj i≮j) j>0)

------------------------------------------------------------------------------
-- The division satisfies the specification.

-- We do the well-founded induction on i and we keep j fixed.
div-DIV : ∀ {i j} → N i → N j → j > zero → DIV i j (div i j)
div-DIV {j = j} Ni Nj j>0 = <-wfind A ih Ni
  where
  A : D → Set
  A d = DIV d j (div d j)

  -- The inductive step doesn't use the variable i (nor Ni). To make
  -- this clear we write down the inductive step using the variables m
  -- and n.
  ih : ∀ {n} → N n → (∀ {m} → N m → m < n → A m) → A n
  ih {n} Nn ah =
    case (div-x<y-DIV Nn Nj) (div-x≮y-DIV Nn Nj ah j>0) (x<y∨x≮y Nn Nj)