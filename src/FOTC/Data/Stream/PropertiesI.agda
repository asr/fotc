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
... | e , es , Ses , h₂ = subst Stream (sym (∧-proj₂ (∷-injective h₂))) Ses

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} xs≈ys = Stream-gfp₂ P₁ helper₁ (ys , xs≈ys)
                         , Stream-gfp₂ P₂ helper₂ (xs , xs≈ys)
  where
  P₁ : D → Set
  P₁ ws = ∃[ zs ] ws ≈ zs

  helper₁ : ∀ {ws} → P₁ ws →
            ∃[ w' ] ∃[ ws' ] P₁ ws' ∧ ws ≡ w' ∷ ws'
  helper₁ {ws} (zs , ws≈zs) with ≈-gfp₁ ws≈zs
  ... | w' , ws' , zs' , ws'≈zs' , ws≡w'∷ws' , _ =
    w' , ws' , (zs' , ws'≈zs') , ws≡w'∷ws'

  P₂ : D → Set
  P₂ zs = ∃[ ws ] ws ≈ zs

  helper₂ : ∀ {zs} → P₂ zs → ∃[ z' ] ∃[ zs' ] P₂ zs' ∧ zs ≡ z' ∷ zs'
  helper₂  {zs} (ws , ws≈zs) with ≈-gfp₁ ws≈zs
  ... | w' , ws' , zs' , ws'≈zs' , _ , zs≡w'∷zs' =
    w' , zs' , (ws' , ws'≈zs') , zs≡w'∷zs'
