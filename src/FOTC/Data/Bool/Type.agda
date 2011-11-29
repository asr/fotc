------------------------------------------------------------------------------
-- The FOTC booleans type
------------------------------------------------------------------------------

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
indBool : (P : D → Set) → P true → P false → ∀ {b} → Bool b → P b
indBool P Pt Pf tB = Pt
indBool P Pt Pf fB = Pf
