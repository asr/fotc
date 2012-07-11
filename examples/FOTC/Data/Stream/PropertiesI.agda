------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.PropertiesI where

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Stream
open import FOTC.Relation.Binary.Bisimilarity

-----------------------------------------------------------------------------

tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
tailS {x} {xs} h₁ with (Stream-gfp₁ h₁)
... | x' , xs' , Sxs' , h₂ = subst Stream (sym (∧-proj₂ (∷-injective h₂))) Sxs'

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} h = Stream-gfp₂ P₁ helper₁ (ys , h)
                       , Stream-gfp₂ P₂ helper₂ (xs , h)
  where
  P₁ : D → Set
  P₁ ws = ∃[ zs ] ws ≈ zs

  helper₁ : ∀ {ws} → P₁ ws → ∃[ w' ] ∃[ ws' ] P₁ ws' ∧ ws ≡ w' ∷ ws'
  helper₁ {ws} (zs , h₁) with ≈-gfp₁ h₁
  ... | w' , ws' , zs' , prf₁ , prf₂ , _ = w' , ws' , (zs' , prf₁) , prf₂

  P₂ : D → Set
  P₂ zs = ∃[ ws ] ws ≈ zs

  helper₂ : ∀ {zs} → P₂ zs → ∃[ z' ] ∃[ zs' ] P₂ zs' ∧ zs ≡ z' ∷ zs'
  helper₂  {zs} (ws , h₁) with ≈-gfp₁ h₁
  ... | w' , ws' , zs' , prf₁ , _ , prf₂ = w' , zs' , (ws' , prf₁) , prf₂
