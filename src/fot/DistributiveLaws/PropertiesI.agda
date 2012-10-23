------------------------------------------------------------------------------
-- Group theory properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.PropertiesI where

open import DistributiveLaws.Base

------------------------------------------------------------------------------
-- Congruence properties

-- The propositional equality is compatible with the binary operation.

-- ·-cong : ∀ {a b c d} → a ≡ b → c ≡ d → a · c ≡ b · d
-- ·-cong = cong₂ _·_

·-leftCong : ∀ {a b c} → a ≡ b → a · c ≡ b · c
·-leftCong refl = refl

·-rightCong : ∀ {a b c} → b ≡ c → a · b ≡ a · c
·-rightCong refl = refl
