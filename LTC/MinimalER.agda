------------------------------------------------------------------------------
-- Identity properties (they are not required when it is used the ATP)
------------------------------------------------------------------------------

module LTC.MinimalER where

open import LTC.Minimal

------------------------------------------------------------------------------

subst : (P : D → Set){x y : D} → x ≡ y → P x → P y
subst P refl px = px
