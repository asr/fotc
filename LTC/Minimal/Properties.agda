------------------------------------------------------------------------------
-- PCF terms properties
------------------------------------------------------------------------------

module LTC.Minimal.Properties where

open import LTC.Minimal

------------------------------------------------------------------------------

postulate
  succInjective : {d e : D} → succ d ≡ succ e → d ≡ e
{-# ATP prove succInjective #-}

postulate
  ∷-injective : {x y xs ys : D} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
{-# ATP prove ∷-injective #-}

