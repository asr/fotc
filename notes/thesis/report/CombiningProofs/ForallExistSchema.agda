{-# OPTIONS --exact-split                       #-}
{-# OPTIONS --no-sized-types                    #-}
{-# OPTIONS --no-universe-polymorphism          #-}
{-# OPTIONS --schematic-propositional-functions #-}
{-# OPTIONS --without-K                         #-}

module CombiningProofs.ForallExistSchema where

open import Common.FOL.FOL-Eq

A : D → Set
A x = x ≡ x ∨ x ≡ x
{-# ATP definition A #-}

postulate ∀→∃₁ : (∀ {x} → A x) → ∃ A
{-# ATP prove ∀→∃₁ #-}

postulate ∀→∃₂ : {A : D → Set} → (∀ {x} → A x) → ∃ A
{-# ATP prove ∀→∃₂ #-}
