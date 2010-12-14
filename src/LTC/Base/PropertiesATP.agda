------------------------------------------------------------------------------
-- PCF terms properties
------------------------------------------------------------------------------

module LTC.Base.PropertiesATP where

open import LTC.Base

open import Common.Function using ( _$_ )

------------------------------------------------------------------------------

postulate
  succInjective : {d e : D} → succ d ≡ succ e → d ≡ e
{-# ATP prove succInjective #-}

postulate
  ∷-injective : {x y xs ys : D} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
{-# ATP prove ∷-injective #-}
