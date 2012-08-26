----------------------------------------------------------------------------
-- The FOTC lists of natural numbers type
----------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.List.Type where

open import FOTC.Base
open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- The FOTC lists of natural numbers type (inductive predicate for
-- total lists of natural numbers).
data ListN : D → Set where
  nilLN  :                             ListN []
  consLN : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)
{-# ATP axiom nilLN consLN #-}
