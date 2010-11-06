------------------------------------------------------------------------------
-- Identity properties (they are not required when the ATPs are used)
------------------------------------------------------------------------------

module LTC.BaseER where

open import LTC.Base

------------------------------------------------------------------------------

subst : (P : D → Set){x y : D} → x ≡ y → P x → P y
subst P refl px = px
