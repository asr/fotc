{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LogicalFramework.Existential where

module LF where
  postulate
    D : Set

    -- Disjunction.
    _∨_  : Set → Set → Set
    inj₁ : {A B : Set} → A → A ∨ B
    inj₂ : {A B : Set} → B → A ∨ B
    case : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C

    -- The existential quantifier type on D.
    ∃       : (A : D → Set) → Set
    _,_     : {A : D → Set}(t : D) → A t → ∃ A
    ∃-proj₁ : {A : D → Set} → ∃ A → D
    ∃-proj₂ : {A : D → Set}(h : ∃ A) → A (∃-proj₁ h)
    ∃-elim  : {A : D → Set}{B : Set} → ∃ A → (∀ {x} → A x → B) → B

  syntax ∃ (λ x → e) = ∃[ x ] e

  module FOL-Examples where
    -- Using the projections.
    ∃∀₁ : {A : D → D → Set} → ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
    ∃∀₁ h y = ∃-proj₁ h , (∃-proj₂ h) y

    ∃∨₁ : {A B : D → Set} → ∃[ x ](A x ∨ B x) → (∃[ x ] A x) ∨ (∃[ x ] B x)
    ∃∨₁ h = case (λ Ax → inj₁ (∃-proj₁ h , Ax))
                 (λ Bx → inj₂ (∃-proj₁ h , Bx))
                 (∃-proj₂ h)

    -- Using the elimination.
    ∃∀₂ : {A : D → D → Set} → ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
    ∃∀₂ h y = ∃-elim h (λ {x} ah → x , ah y)

    ∃∨₂ : {A B : D → Set} → ∃[ x ](A x ∨ B x) → (∃[ x ] A x) ∨ (∃[ x ] B x)
    ∃∨₂ h = ∃-elim h (λ {x} ah → case (λ Ax → inj₁ (x , Ax))
                                      (λ Bx → inj₂ (x , Bx))
                                      ah)

  module NonFOL-Examples where

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

  module FOL-Examples where
    -- Using the projections.
    ∃∀₁ : {A : D → D → Set} → ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
    ∃∀₁ h y = ∃-proj₁ h , (∃-proj₂ h) y

    ∃∨₁ : {A B : D → Set} → ∃[ x ](A x ∨ B x) → (∃[ x ] A x) ∨ (∃[ x ] B x)
    ∃∨₁ h = case (λ Ax → inj₁ (∃-proj₁ h , Ax))
                 (λ Bx → inj₂ (∃-proj₁ h , Bx))
                 (∃-proj₂ h)

    -- Using the elimination.
    ∃∀₂ : {A : D → D → Set} → ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
    ∃∀₂ h y = ∃-elim h (λ {x} ah → x , ah y)

    ∃∨₂ : {A B : D → Set} → ∃[ x ](A x ∨ B x) → (∃[ x ] A x) ∨ (∃[ x ] B x)
    ∃∨₂ h = ∃-elim h (λ {x} ah → case (λ Ax → inj₁ (x , Ax))
                                      (λ Bx → inj₂ (x , Bx))
                                      ah)

    -- Using pattern matching.
    ∃∀₃ : {A : D → D → Set} → ∃[ x ](∀ y → A x y) → ∀ y → ∃[ x ] A x y
    ∃∀₃ (x , Ax) y = x , Ax y

    ∃∨₃ : {A B : D → Set} → ∃[ x ](A x ∨ B x) → (∃[ x ] A x) ∨ (∃[ x ] B x)
    ∃∨₃ (x , inj₁ Ax) = inj₁ (x , Ax)
    ∃∨₃ (x , inj₂ Bx) = inj₂ (x , Bx)

  module NonFOL-Examples where

    -- Using the projections.
    non-FOL₁ : {A : D → Set} → ∃ A → D
    non-FOL₁ h = ∃-proj₁ h

    -- Using the elimination.
    non-FOL₂ : {A : D → Set} → ∃ A → D
    non-FOL₂ h = ∃-elim h (λ {x} _ → x)

    -- Using the pattern matching.
    non-FOL₃ : {A : D → Set} → ∃ A → D
    non-FOL₃ (x , _) = x
