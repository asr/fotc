------------------------------------------------------------------------------
-- The division program satisfies the specification
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

-- This module proves the correctness of the division program using
-- repeated subtraction.

-- Peter Dybjer. Program verification in a logical theory of
-- constructions. In Jean-Pierre Jouannaud, editor. Functional
-- Programming Languages and Computer Architecture, volume 201 of
-- LNCS, 1985, pages 334-349. Appears in revised form as Programming
-- Methodology Group Report 26, June 1986.

-- N.B This module does not contain combined proofs, but it imports
-- modules which contain combined proofs.

module LTC-PCF.Program.Division.ProofSpecificationATP where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
open import LTC-PCF.Data.Nat.PropertiesATP

import LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionATP
open module WFInd = LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionATP.WFInd

open import LTC-PCF.Program.Division.Division
open import LTC-PCF.Program.Division.IsCorrectATP
open import LTC-PCF.Program.Division.Specification
open import LTC-PCF.Program.Division.TotalityATP

------------------------------------------------------------------------------
-- The division result satifies the specification DIV
-- when the dividend is less than the divisor.
div-x<y-DIV : ∀ {i j} → N i → N j → LT i j → DIV i j (div i j)
div-x<y-DIV Ni Nj i<j = div-x<y-N i<j , div-x<y-correct Ni Nj i<j

-- The division result satisfies the specification DIV when the
-- dividend is greater or equal than the divisor.
div-x≮y-DIV : ∀ {i j} → N i → N j →
              (∀ {i'} → N i' → LT i' i → DIV i' j (div i' j)) →
              GT j zero →
              NLT i j →
              DIV i j (div i j)
div-x≮y-DIV {i} {j} Ni Nj accH j>0 i≮j =
  div-x≮y-N ih i≮j , div-x≮y-correct Ni Nj ih i≮j

  where
  -- The inductive hypothesis on i ∸ j.
  ih : DIV (i ∸ j) j (div (i ∸ j) j)
  ih = accH {i ∸ j}
            (∸-N Ni Nj)
            (x≥y→y>0→x∸y<x Ni Nj (x≮y→x≥y Ni Nj i≮j) j>0)

------------------------------------------------------------------------------
-- The division satisfies the specification.

-- We do the well-founded induction on i and we keep j fixed.
div-DIV : ∀ {i j} → N i → N j → GT j zero → DIV i j (div i j)
div-DIV {j = j} Ni Nj j>0 = wfInd-LT P ih Ni
  where
  P : D → Set
  P d = DIV d j (div d j)

  -- The inductive step doesn't use the variable i (nor Ni). To make
  -- this clear we write down the inductive step using the variables m
  -- and n.
  ih : ∀ {n} → N n → (accH : ∀ {m} → N m → LT m n → P m) → P n
  ih {n} Nn accH =
    [ div-x<y-DIV Nn Nj , div-x≮y-DIV Nn Nj accH j>0 ] (x<y∨x≮y Nn Nj)
