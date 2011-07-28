------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

module FOTC.Data.Stream.PropertiesATP where

open import FOTC.Base

open import FOTC.Base.PropertiesATP

open import FOTC.Data.Stream.Type

open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} xs≈ys = Stream-gfp₂ P₁ helper₁ (ys , xs≈ys)
                         , Stream-gfp₂ P₂ helper₂ (xs , xs≈ys)
  where
  P₁ : D → Set
  P₁ ws = ∃ λ zs → ws ≈ zs

  P₂ : D → Set
  P₂ zs = ∃ λ ws → ws ≈ zs
  {-# ATP definition P₂ #-}

  -- TODO: We don't use the predicate P₁ in the type of the function
  -- helper₁, because at the moment the agda2atp tool doesn't handle
  -- the eta-expansion for equations.
  postulate
    helper₁ : ∀ {ws} → (∃ λ zs → ws ≈ zs) →
              ∃ (λ w' → ∃ (λ ws' → ws ≡ w' ∷ ws' ∧ (∃ λ zs → ws' ≈ zs)))
  {-# ATP prove helper₁ #-}

  postulate
    helper₂ : ∀ {zs} → P₂ zs →
              ∃ (λ z' → ∃ (λ zs' → zs ≡ z' ∷ zs' ∧ P₂ zs'))
  {-# ATP prove helper₂ #-}
