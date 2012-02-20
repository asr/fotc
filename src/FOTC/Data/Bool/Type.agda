------------------------------------------------------------------------------
-- The FOTC booleans type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module is re-exported by FOTC.Data.Bool.

module FOTC.Data.Bool.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- The FOTC booleans type.
data Bool : D → Set where
  tB : Bool true
  fB : Bool false
{-# ATP axiom tB fB #-}

-- The rule of proof by case analysis on Bool.
Bool-ind : (P : D → Set) → P true → P false → ∀ {b} → Bool b → P b
Bool-ind P Pt Pf tB = Pt
Bool-ind P Pt Pf fB = Pf
