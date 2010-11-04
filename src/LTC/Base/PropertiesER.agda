------------------------------------------------------------------------------
-- PCF terms properties (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Base.PropertiesER where

open import LTC.Base

------------------------------------------------------------------------------
-- See the ATP proof.
postulate
  succInjective : {d e : D} → succ d ≡ succ e → d ≡ e

-- See the ATP proof.
postulate
  ∷-injective : {x y xs ys : D} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
