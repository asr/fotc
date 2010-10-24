------------------------------------------------------------------------------
-- PCF terms properties (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Minimal.PropertiesER where

open import LTC.Minimal
-- open import LTC.MinimalER using ( subst )

------------------------------------------------------------------------------
-- See the ATP proof.
postulate
  succInjective : {d e : D} → succ d ≡ succ e → d ≡ e

-- See the ATP proof.
postulate
  ∷-injective : {x y xs ys : D} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
