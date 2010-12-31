------------------------------------------------------------------------------
-- Parametrized equality reasoning
------------------------------------------------------------------------------

module Common.Relation.Binary.EqReasoning
  {D     : Set}
  (_≡_   : D → D → Set)
  (refl  : {x : D} → x ≡ x)
  (trans : {x y z : D} → x ≡ y → y ≡ z → x ≡ z)
  where

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
