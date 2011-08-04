------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

module FOTC.Data.Stream.PropertiesATP where

open import FOTC.Base

open import FOTC.Base.PropertiesATP

open import FOTC.Data.Stream.Type

open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

postulate tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
{-# ATP prove tailS #-}

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} xs≈ys = Stream-gfp₂ P₁ helper₁ (ys , xs≈ys)
                         , Stream-gfp₂ P₂ helper₂ (xs , xs≈ys)
  where
  P₁ : D → Set
  P₁ ws = ∃ λ zs → ws ≈ zs
  {-# ATP definition P₁ #-}

  P₂ : D → Set
  P₂ zs = ∃ λ ws → ws ≈ zs
  {-# ATP definition P₂ #-}

  postulate
    helper₁ : ∀ {ws} → P₁ ws → ∃ λ w' → ∃ λ ws' → P₁ ws' ∧ ws ≡ w' ∷ ws'
  {-# ATP prove helper₁ #-}

  postulate
    helper₂ : ∀ {zs} → P₂ zs → ∃ λ z' → ∃ λ zs' → P₂ zs' ∧ zs ≡ z' ∷ zs'
  {-# ATP prove helper₂ #-}
