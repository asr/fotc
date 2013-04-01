------------------------------------------------------------------------------
-- Common properties for the alternating bit protocol
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.ABP.PropertiesI where

open import FOTC.Base
open import FOTC.Program.ABP.ABP

------------------------------------------------------------------------------
-- Congruence properties

awaitCong₄ : ∀ {b i is ds₁ ds₂} → ds₁ ≡ ds₂ →
             await b i is ds₁ ≡ await b i is ds₂
awaitCong₄ refl = refl
