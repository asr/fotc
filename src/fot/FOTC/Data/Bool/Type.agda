------------------------------------------------------------------------------
-- The FOTC Booleans type
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- N.B. This module is re-exported by FOTC.Data.Bool.

module FOTC.Data.Bool.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- The FOTC Booleans type (inductive predicate for total Booleans).
data Bool : D → Set where
  btrue  : Bool true
  bfalse : Bool false
{-# ATP axioms btrue bfalse #-}

-- The rule of proof by case analysis.
Bool-ind : (A : D → Set) → A true → A false → ∀ {b} → Bool b → A b
Bool-ind A At Af btrue  = At
Bool-ind A At Af bfalse = Af
