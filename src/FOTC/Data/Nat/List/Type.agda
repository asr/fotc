----------------------------------------------------------------------------
-- The FOTC list of natural numbers type
----------------------------------------------------------------------------

module FOTC.Data.Nat.List.Type where

open import FOTC.Base

open import FOTC.Data.Nat.Type
  using ( N  -- The FOTC list of natural numbers type.
        )

------------------------------------------------------------------------------
-- The FOTC list of natural numbers type.
data ListN : D → Set where
  nilLN  :                                      ListN []
  consLN : ∀ {n ns} → N n → (LNns : ListN ns) → ListN (n ∷ ns)
{-# ATP hint nilLN #-}
{-# ATP hint consLN #-}
