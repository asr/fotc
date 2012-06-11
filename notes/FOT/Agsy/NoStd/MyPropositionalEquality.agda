------------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of Agda on 07 February 2012.

module MyPropositionalEquality where

-- We add 3 to the fixities of the standard library.
infix 7 _≡_

------------------------------------------------------------------------------

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

-- Identity properties

sym : ∀ {A} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

cong : {A B : Set} (f : A → B) → ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

module ≡-Reasoning where
  -- We add 3 to the fixities of the standard library.
  infix  7 _≃_
  infix  4 begin_
  infixr 5 _≡⟨_⟩_
  infix  5 _∎

  ----------------------------------------------------------------------------
  -- Adapted from the standard library (Relation.Binary.PreorderReasoning).
  private
    data _≃_ {A : Set}(x y : A) : Set where
      prf : x ≡ y → x ≃ y

  begin_ : {A : Set}{x y : A} → x ≃ y → x ≡ y
  begin prf x≡y = x≡y

  _≡⟨_⟩_ : {A : Set}(x : A){y z : A} → x ≡ y → y ≃ z → x ≃ z
  _ ≡⟨ x≡y ⟩ prf y≡z = prf (trans x≡y y≡z)

  _∎ : {A : Set}(x : A) → x ≃ x
  _∎ _ = prf refl
