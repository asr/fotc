------------------------------------------------------------------------------
-- The division program is correct
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module proves the correctness of the division program using
-- repeated subtraction (Dybjer 1985).

-- Peter Dybjer. Program verification in a logical theory of
-- constructions. In Jean-Pierre Jouannaud, editor. Functional
-- Programming Languages and Computer Architecture, volume 201 of
-- LNCS, 1985, pages 334-349. Appears in revised form as Programming
-- Methodology Group Report 26, June 1986.

module LTC-PCF.Program.Division.CorrectnessProof where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.Properties
open import LTC-PCF.Data.Nat.Properties

import LTC-PCF.Data.Nat.Induction.NonAcc.WF
open module WFInd = LTC-PCF.Data.Nat.Induction.NonAcc.WF.WFInd

open import LTC-PCF.Program.Division.Division
open import LTC-PCF.Program.Division.Specification
open import LTC-PCF.Program.Division.Result
open import LTC-PCF.Program.Division.Totality

------------------------------------------------------------------------------
-- The division program is correct when the dividend is less than the
-- divisor.
div-x<y-correct : ∀ {i j} → N i → N j → i < j → divSpec i j (div i j)
div-x<y-correct Ni Nj i<j = div-x<y-N i<j , div-x<y-resultCorrect Ni Nj i<j

-- The division program is correct when the dividend is greater or
-- equal than the divisor.
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
