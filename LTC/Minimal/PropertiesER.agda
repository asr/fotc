------------------------------------------------------------------------------
-- PCF terms properties (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Minimal.PropertiesER where

open import LTC.Minimal
-- open import LTC.MinimalER using ( subst )

------------------------------------------------------------------------------
-- See the ATP proof.
postulate
  succInjectivity : {d e : D} → succ d ≡ succ e → d ≡ e
