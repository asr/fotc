{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LogicalFramework.AdequacyTheorems where

-- First-order logic with equality.
open import Common.FOL.FOL-Eq public

module Example10 where
  postulate
    A B C : Set
    d : A → C
    e : B → C

  f : A ∨ B → C
  f (inj₁ a) = d a
  f (inj₂ b) = e b

  f' : A ∨ B → C
  f' = case d e

module Example20 where

  f : {A : D → Set}{t t' : D} → t ≡ t' → A t → A t'
  f {A} {t} {.t} refl At = d At
    where
    postulate d : A t → A t

  f' : {A : D → Set}{t t' : D} → t ≡ t' → A t → A t'
  f' {A} h At = subst A h At
