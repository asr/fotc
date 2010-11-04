------------------------------------------------------------------------------
-- Identity properties (they are not required when it is used the ATP)
------------------------------------------------------------------------------

module LTC.BaseER where

open import LTC.Base

------------------------------------------------------------------------------

subst : (P : D → Set){x y : D} → x ≡ y → P x → P y
subst P refl px = px
