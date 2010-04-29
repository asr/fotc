------------------------------------------------------------------------------
-- Identity properties (they are not requiried when it is used the ATP)
------------------------------------------------------------------------------

module LTC.MinimalER where

open import LTC.Minimal

subst : (P : D → Set){x y : D} → x ≡ y → P x → P y
subst P refl px = px

sym : {x y : D} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : D} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z
