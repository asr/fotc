------------------------------------------------------------------------------
-- Distributive laws properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.DistributiveLaws.Properties where

open import Interactive.DistributiveLaws.Base

------------------------------------------------------------------------------
-- Congruence properties

-- The propositional equality is compatible with the binary operation.

·-leftCong : ∀ {a b c} → a ≡ b → a · c ≡ b · c
·-leftCong refl = refl

·-rightCong : ∀ {a b c} → b ≡ c → a · b ≡ a · c
·-rightCong refl = refl
