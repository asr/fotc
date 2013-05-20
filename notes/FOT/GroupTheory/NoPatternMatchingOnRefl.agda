------------------------------------------------------------------------------
-- Proving properties without using pattern matching on refl
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.GroupTheory.NoPatternMatchingOnRefl where

open import GroupTheory.Base

------------------------------------------------------------------------------
-- From GroupTheory.PropertiesI

-- Congruence properties

-- The propositional equality is compatible with the binary operation.

·-leftCong : ∀ {a b c} → a ≡ b → a · c ≡ b · c
·-leftCong {a} {c = c} h = subst (λ t → a · c ≡ t · c ) h refl

·-rightCong : ∀ {a b c} → b ≡ c → a · b ≡ a · c
·-rightCong {a} {b} h = subst (λ t → a · b ≡ a · t) h refl

-- The propositional equality is compatible with the inverse function.
⁻¹-cong : ∀ {a b} → a ≡ b → a ⁻¹ ≡ b ⁻¹
⁻¹-cong {a} h = subst (λ t → a ⁻¹ ≡ t ⁻¹) h refl
