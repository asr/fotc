----------------------------------------------------------------------------
-- The LTC list of natural numbers type
----------------------------------------------------------------------------

module LTC.Data.Nat.List.Type where

open import LTC.Minimal

open import LTC.Data.Nat.Type using ( N )

------------------------------------------------------------------------------
-- The LTC list of natural numbers type.
data ListN : D → Set where
  nilLN  : ListN []
  consLN : {n ns : D} → N n → (LNns : ListN ns) → ListN (n ∷ ns)
{-# ATP hint nilLN #-}
{-# ATP hint consLN #-}
