------------------------------------------------------------------------------
-- The LTC stream type
------------------------------------------------------------------------------

module LTC.Data.Stream.Type where

open import LTC.Minimal

------------------------------------------------------------------------------
-- TODO: This should be a coinductive type.
-- The LTC stream type.
data Stream : D → Set where
  consS : (x : D){xs : D} → (Sxs : Stream xs) → Stream (x ∷ xs)
