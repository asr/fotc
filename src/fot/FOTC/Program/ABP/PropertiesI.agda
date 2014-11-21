------------------------------------------------------------------------------
-- Common properties for the alternating bit protocol
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.ABP.PropertiesI where

open import FOTC.Base
open import FOTC.Program.ABP.ABP

------------------------------------------------------------------------------
-- Congruence properties

awaitCong₄ : ∀ {b i is ds₁ ds₂} → ds₁ ≡ ds₂ →
             await b i is ds₁ ≡ await b i is ds₂
awaitCong₄ refl = refl

corruptCong : ∀ {os₁ os₂} → os₁ ≡ os₂ → corrupt os₁ ≡ corrupt os₂
corruptCong refl = refl
