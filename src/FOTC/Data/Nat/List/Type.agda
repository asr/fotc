----------------------------------------------------------------------------
-- The FOTC list of natural numbers type
----------------------------------------------------------------------------

module FOTC.Data.Nat.List.Type where

open import FOTC.Base

open import FOTC.Data.Nat.Type

------------------------------------------------------------------------------
-- The FOTC list of natural numbers type.
data ListN : D → Set where
  nilLN  :                             ListN []
  consLN : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)
{-# ATP axiom nilLN #-}
{-# ATP axiom consLN #-}
