------------------------------------------------------------------------------
-- Equality reasoning on the universe of discourse.
------------------------------------------------------------------------------

module Common.Relation.Binary.EqReasoning where

open import Common.Relation.Binary.PropositionalEquality using ( _≡_ ; refl )
open import Common.Relation.Binary.PropositionalEquality.Properties
  using ( trans )
open import Common.Universe using ( D )

-- We add 3 to the fixities of the standard library.
infix 7 _≃_
infix  4 begin_
infixr 5 _≡⟨_⟩_
infix  5 _∎

------------------------------------------------------------------------------
-- Adapted from the standard library (Relation.Binary.PreorderReasoning).
private
  data _≃_ (x y : D) : Set where
    prf : x ≡ y → x ≃ y

begin_ : {x y : D} → x ≃ y → x ≡ y
begin prf x≡y = x≡y

_≡⟨_⟩_ : (x : D){y z : D} → x ≡ y → y ≃ z → x ≃ z
_ ≡⟨ x≡y ⟩ prf y≡z = prf (trans x≡y y≡z)

_∎ : (x : D) → x ≃ x
_∎ _ = prf refl
