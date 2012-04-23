-- Tested with FOT on 23 April 2012.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Existential where

module LF where
  postulate
    D       : Set
    ∃       : (A : D → Set) → Set
    _,_     : {A : D → Set}(x : D) → A x → ∃ A
    ∃-proj₁ : {A : D → Set} → ∃ A → D
    ∃-proj₂ : {A : D → Set}(h : ∃ A) → A (∃-proj₁ h)
    ∃-elim  : {A : D → Set}{B : Set} → ∃ A → (∀ {x} → A x → B) → B

  syntax ∃ (λ x → e) = ∃[ x ] e

  module FOL-Example where
    postulate A : D → D → Set

    -- Using the projections.
    ∃∀₁ : ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
    ∃∀₁ h y = ∃-proj₁ h , (∃-proj₂ h) y

    -- Using the elimination
    ∃∀₂ : ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
    ∃∀₂ h y = ∃-elim h (λ {x} h₁ → x , h₁ y)

  module NonFOL-Example where

    -- Using the projections.
    non-FOL₁ : {A : D → Set} → ∃ A → D
    non-FOL₁ h = ∃-proj₁ h

    -- Using the elimination.
    non-FOL₂ : {A : D → Set} → ∃ A → D
    non-FOL₂ h = ∃-elim h (λ {x} _ → x)

module Inductive where

  open import Common.FOL.FOL

  -- The existential proyections.
  ∃-proj₁ : ∀ {A} → ∃ A → D
  ∃-proj₁ (x , _) = x

  ∃-proj₂ : ∀ {A} → (h : ∃ A) → A (∃-proj₁ h)
  ∃-proj₂ (_ , Ax) = Ax

  -- The existential elimination.
  ∃-elim : {A : D → Set}{B : Set} → ∃ A → (∀ {x} → A x → B) → B
  ∃-elim (_ , Ax) h = h Ax

  module FOL-Example where
    postulate A : D → D → Set

    -- Using the projections.
    ∃∀₁ : ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
    ∃∀₁ h y = ∃-proj₁ h , (∃-proj₂ h) y

    -- Using the elimination.
    ∃∀₂ : ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
    ∃∀₂ h y = ∃-elim h (λ {x} h₁ → x , h₁ y)

    -- Using pattern matching.
    ∃∀₃ : ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
    ∃∀₃ (x , Ax) y = x , Ax y

  module NonFOL-Example where

    -- Using the projections.
    non-FOL₁ : {A : D → Set} → ∃ A → D
    non-FOL₁ h = ∃-proj₁ h

    -- Using the elimination.
    non-FOL₂ : {A : D → Set} → ∃ A → D
    non-FOL₂ h = ∃-elim h (λ {x} _ → x)

    -- Using the pattern matching.
    non-FOL₃ : {A : D → Set} → ∃ A → D
    non-FOL₃ (x , _) = x
