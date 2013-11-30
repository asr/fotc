------------------------------------------------------------------------------
-- Common properties for the alternating bit protocol
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Program.ABP.DS.PropertiesI where

open import FOT.FOTC.Program.ABP.DS.ABP

open import FOTC.Base


------------------------------------------------------------------------------
-- Congruence properties

awaitCong₄ : ∀ {b i is ds₁ ds₂} → ds₁ ≡ ds₂ →
             await b i is ds₁ ≡ await b i is ds₂
awaitCong₄ refl = refl

corruptCong : ∀ {os₁ os₂} → os₁ ≡ os₂ → corrupt os₁ ≡ corrupt os₂
corruptCong refl = refl
