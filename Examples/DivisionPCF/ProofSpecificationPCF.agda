------------------------------------------------------------------------------
-- The division program satisfies the specification
------------------------------------------------------------------------------

-- This module proves the correctness of the division program using
-- repeated subtraction.

-- Peter Dybjer. Program verification in a logical theory of
-- constructions. In Jean-Pierre Jouannaud, editor. Functional
-- Programming Languages and Computer Architecture, volume 201 of
-- LNCS, 1985, pages 334-349. Appears in revised form as Programming
-- Methodology Group Report 26, June 1986.

module Examples.DivisionPCF.ProofSpecificationPCF where

open import LTC.Minimal

open import Examples.DivisionPCF.DivisionPCF using ( div )
open import Examples.DivisionPCF.IsCorrectPCF using
  ( div-x<y-correct ; div-x≥y-correct)
open import Examples.DivisionPCF.IsN-PCF using
  ( div-x<y-N ; div-x≥y-N )
open import Examples.DivisionPCF.SpecificationPCF using ( DIV )

open import LTC-PCF.DataPCF.NatPCF using ( _-_ ; N )
open import LTC-PCF.DataPCF.NatPCF.InductionPCF.WellFoundedPCF using
  ( wfIndN-LT )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF using ( GE ; GT ; LT )
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF.PropertiesPCF using
  ( x≥y→y>0→x-y<x
  ; x<y∨x≥y
  )
open import LTC-PCF.DataPCF.NatPCF.PropertiesPCF using ( minus-N )

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
  (div-x≥y-N Ni Nj ih i≥j) , div-x≥y-correct Ni Nj ih i≥j

    where
    -- The inductive hypothesis on 'i - j'.
    ih : DIV (i - j) j (div (i - j) j)
    ih = accH {i - j}
              (minus-N Ni Nj)
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
