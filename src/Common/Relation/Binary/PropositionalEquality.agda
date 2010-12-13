------------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------------

module Common.Relation.Binary.PropositionalEquality where

open import Common.Universe using ( D )

-- We add 3 to the fixities of the standard library.
infix  7 _≡_

------------------------------------------------------------------------------
-- The identity type on the universe of discourse.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- Identity properties

sym : {x y : D} → x ≡ y → y ≡ x
sym refl = refl

trans : {x y z : D} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

subst : (P : D → Set){x y : D} → x ≡ y → P x → P y
subst P refl px = px
