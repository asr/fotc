------------------------------------------------------------------------------
-- Group theory congruence proofs using pattern matching
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LogicalFramework.GroupCongruence where

open import GroupTheory.Base

·-cong : ∀ {a b c d} → a ≡ b → c ≡ d → a · c ≡ b · d
·-cong refl refl = refl

·-leftCong : ∀ {a b c} → a ≡ b → a · c ≡ b · c
·-leftCong refl = refl

·-rightCong : ∀ {a b c} → b ≡ c → a · b ≡ a · c
·-rightCong refl = refl

⁻¹-cong : ∀ {a b} → a ≡ b → a ⁻¹ ≡ b ⁻¹
⁻¹-cong refl = refl
