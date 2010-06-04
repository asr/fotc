------------------------------------------------------------------------------
-- The division satisfies the specification
------------------------------------------------------------------------------

-- This module formalize the division algorithm following [1].
-- [1] Peter Dybjer. Program verification in a logical theory of
-- constructions. In Jean-Pierre Jouannaud, editor. Functional
-- Programming Languages and Computer Architecture, volume 201 of
-- LNCS, 1985, pages 334-349. Appears in revised form as Programming
-- Methodology Group Report 26, June 1986.

module Examples.Division.IsDIV-ER where

open import LTC.Minimal

open import Examples.Division
open import Examples.Division.EquationsER
open import Examples.Division.IsCorrectER
open import Examples.Division.IsN-ER
open import Examples.Division.Specification

open import LTC.Data.N
open import LTC.Data.N.Induction.WellFoundedPCF
open import LTC.Function.ArithmeticPCF
open import LTC.Function.Arithmetic.PropertiesPCF-ER
open import LTC.Relation.InequalitiesPCF
open import LTC.Relation.Inequalities.PropertiesPCF-ER

------------------------------------------------------------------------------

-- The division result satifies the specification DIV
-- when the dividend is less than the divisor
div-x<y-DIV : {i j : D} → N i → N j -> LT i j → DIV i j (div i j)
div-x<y-DIV Ni Nj i<j = div-x<y-N i<j , div-x<y-correct Ni Nj i<j

-- The division result satisfies the specification DIV when the
-- dividend is greater or equal than the divisor.
div-x≥y-DIV : {i j : D} → N i -> N j →
              ({i' : D} → N i' → LT i' i → DIV i' j (div i' j)) →
              GT j zero →
              GE i j →
              DIV i j (div i j)
div-x≥y-DIV {i} {j} Ni Nj accH j>0 i≥j =
  (div-x≥y-N ih i≥j) , div-x≥y-correct Ni Nj ih i≥j

    where
    -- The inductive hypothesis on 'i - j'.
    ih : DIV (i - j) j (div (i - j) j)
    ih = accH {i - j}
              (minus-N Ni Nj )
              (x≥y→y>0→x-y<x Ni Nj i≥j j>0)

------------------------------------------------------------------------------
-- The division satisfies the specification

-- We do the well-founded induction on 'i' and we keep 'j' fixed.
div-DIV : {i j : D} → N i → N j → GT j zero → DIV i j (div i j)
div-DIV {j = j} Ni Nj j>0 = wfIndN-LT P iStep Ni

   where
     P : D → Set
     P d = DIV d j (div d j)

     -- The inductive step doesn't use the variable 'i'
     -- (nor 'Ni'). To make this
     -- clear we write down the inductive step using the variables
     -- 'm' and 'n'.
     iStep : {n : D} → N n →
             (accH : {m : D} → N m → LT m n → P m) →
             P n
     iStep {n} Nn accH =
       [ div-x<y-DIV Nn Nj , div-x≥y-DIV Nn Nj accH j>0 ] (x<y∨x≥y Nn Nj)
