------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality

-----------------------------------------------------------------------------

tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS {x} {xs} h₁ with (Stream-gfp₁ h₁)
... | ∃-intro (∃-intro (Sxs' , h₂)) =
  subst Stream (sym (∧-proj₂ (∷-injective h₂))) Sxs'

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream h = Stream-gfp₂ P₁ helper₁ (∃-intro h)
             , Stream-gfp₂ P₂ helper₂ (∃-intro h)
  where
  P₁ : D → Set
  P₁ ws = ∃[ zs ] ws ≈ zs

  helper₁ : ∀ {ws} → P₁ ws → ∃[ w' ] ∃[ ws' ] P₁ ws' ∧ ws ≡ w' ∷ ws'
  helper₁ (∃-intro h₁) with ≈-gfp₁ h₁
  ... | ∃-intro (∃-intro (∃-intro (prf₁ , prf₂ , _))) =
    ∃-intro (∃-intro ((∃-intro prf₁) , prf₂))

  P₂ : D → Set
  P₂ zs = ∃[ ws ] ws ≈ zs

  helper₂ : ∀ {zs} → P₂ zs → ∃[ z' ] ∃[ zs' ] P₂ zs' ∧ zs ≡ z' ∷ zs'
  helper₂ (∃-intro h₁) with ≈-gfp₁ h₁
  ... | ∃-intro (∃-intro (∃-intro (prf₁ , _ , prf₂))) =
    ∃-intro (∃-intro ((∃-intro prf₁) , prf₂))
