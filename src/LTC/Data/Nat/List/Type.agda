----------------------------------------------------------------------------
-- The LTC list of natural numbers type
----------------------------------------------------------------------------

module LTC.Data.Nat.List.Type where

open import LTC.Base

open import LTC.Data.Nat.Type
  using ( N  -- The LTC list of natural numbers type.
        )

------------------------------------------------------------------------------
-- The LTC list of natural numbers type.
data ListN : D → Set where
  nilLN  : ListN []
  consLN : ∀ {n ns} → N n → (LNns : ListN ns) → ListN (n ∷ ns)
{-# ATP hint nilLN #-}
{-# ATP hint consLN #-}
