------------------------------------------------------------------------------
-- Existential quantifier: pattern matching vs elimination
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with FOT on 19 February 2012.

module Draft.FOTC.Data.Stream.Existential where

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality

------------------------------------------------------------------------------

-- A proof using pattern matching (via the with mechanism).
tailS₁ : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS₁ {x} {xs} h₁ with (Stream-gfp₁ h₁)
... | x' , xs' , Sxs' , h₂ = subst Stream (sym (∧-proj₂ (∷-injective h₂))) Sxs'

-- A proof using existential elimination.
tailS₂ : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS₂ {x} {xs} h =
  ∃-elim (Stream-gfp₁ h)
    (λ x' prf₁ → ∃-elim prf₁
       (λ xs' prf₂ → subst Stream
                          (sym (∧-proj₂ (∷-injective (∧-proj₂ prf₂))))
                          (∧-proj₁ prf₂)))

-- A proof using existential elimination with helper functions.
tailS₃ : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS₃ {x} {xs} h = ∃-elim (Stream-gfp₁ h) helper₁
  where
  helper₁ : ∀ x' → ∃ (λ xs' → Stream xs' ∧ x ∷ xs ≡ x' ∷ xs') → Stream xs
  helper₁ x' h₁ = ∃-elim h₁ helper₂
    where
    helper₂ : ∀ xs' → Stream xs' ∧ x ∷ xs ≡ x' ∷ xs' → Stream xs
    helper₂ xs' (Sxs' , h₂) = subst Stream (sym (∧-proj₂ (∷-injective h₂))) Sxs'
