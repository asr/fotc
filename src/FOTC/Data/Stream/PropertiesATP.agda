------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.PropertiesATP
open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality

------------------------------------------------------------------------------

postulate tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
{-# ATP prove tailS #-}

-- The next couple of predicates are not inside the where clause
-- because the translation of projection-like functions is not
-- implemented.
≈→Stream-P₁ : D → Set
≈→Stream-P₁ ws = ∃[ zs ] ws ≈ zs
{-# ATP definition ≈→Stream-P₁ #-}

≈→Stream-P₂ : D → Set
≈→Stream-P₂ zs = ∃[ ws ] ws ≈ zs
{-# ATP definition ≈→Stream-P₂ #-}

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream xs≈ys = Stream-gfp₂ ≈→Stream-P₁ helper₁ (∃-intro xs≈ys)
                 , Stream-gfp₂ ≈→Stream-P₂ helper₂ (∃-intro xs≈ys)
  where
  postulate
    helper₁ : ∀ {ws} → ≈→Stream-P₁ ws →
              ∃[ w' ] ∃[ ws' ] ≈→Stream-P₁ ws' ∧ ws ≡ w' ∷ ws'
  {-# ATP prove helper₁ #-}

  postulate
    helper₂ : ∀ {zs} → ≈→Stream-P₂ zs →
              ∃[ z' ] ∃[ zs' ] ≈→Stream-P₂ zs' ∧ zs ≡ z' ∷ zs'
  {-# ATP prove helper₂ #-}
