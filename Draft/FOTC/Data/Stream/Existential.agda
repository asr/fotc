------------------------------------------------------------------------------
-- Existential quantifier: pattern matching vs elimination
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with FOT on 17 February 2012.

module Draft.FOTC.Data.Stream.Existential where

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality

------------------------------------------------------------------------------

-- A proof using pattern matching (via the with mechanisms).
tailS₁ : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS₁ {x} {xs} h₁ with (Stream-gfp₁ h₁)
... | e , es , Ses , h₂ = subst Stream (sym (∧-proj₂ (∷-injective h₂))) Ses

-- A proof using elimination.
tailS₂ : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS₂ {x} {xs} h =
  ∃-elim (Stream-gfp₁ h)
    (λ e prf₁ → ∃-elim prf₁
       (λ es prf₂ → subst Stream
                          (sym (∧-proj₂ (∷-injective (∧-proj₂ prf₂))))
                          (∧-proj₁ prf₂)))
