{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LogicalFramework.AdequacyTheorems where

-- First-order logic with equality.
open import Common.FOL.FOL-Eq public

module Example10 where
  postulate
    A B C : Set
    f₁ : A → C
    f₂ : B → C

  f : A ∨ B → C
  f (inj₁ a) = f₁ a
  f (inj₂ b) = f₂ b

  f' : A ∨ B → C
  f' = case f₁ f₂

module Example20 where

  f : {A : D → Set}{t t' : D} → t ≡ t' → A t → A t'
  f {A} {t} {.t} refl At = d At
    where
    postulate d : A t → A t

  f' : {A : D → Set}{t t' : D} → t ≡ t' → A t → A t'
  f' {A} h At = subst A h At

module Example30 where
  postulate
    A B C E : Set
    f₁ : A → E
    f₂ : B → E
    f₃ : C → E

  f : (A ∨ B) ∨ C → E
  f (inj₁ (inj₁ a)) = f₁ a
  f (inj₁ (inj₂ b)) = f₂ b
  f (inj₂ c)        = f₃ c

  f' : (A ∨ B) ∨ C → E
  f' = case (case f₁ f₂) f₃
