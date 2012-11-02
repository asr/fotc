------------------------------------------------------------------------------
-- Streams properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.PropertiesATP where

open import FOTC.Base
open FOTC.Base.BList
open import FOTC.Base.PropertiesATP
open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.List
open import FOTC.Data.Stream
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

postulate tailS : ∀ {x xs} → Stream (x ∷ xs) → Stream xs
{-# ATP prove tailS #-}

≈→Stream : ∀ {xs ys} → xs ≈ ys → Stream xs ∧ Stream ys
≈→Stream {xs} {ys} h = Stream-coind P₁ h₁ (ys , h) , Stream-coind P₂ h₂ (xs , h)
  where
  P₁ : D → Set
  P₁ ws = ∃[ zs ] ws ≈ zs
  {-# ATP definition P₁ #-}

  postulate h₁ : ∀ {ws} → P₁ ws → ∃[ w' ] ∃[ ws' ] P₁ ws' ∧ ws ≡ w' ∷ ws'
  {-# ATP prove h₁ #-}

  P₂ : D → Set
  P₂ zs = ∃[ ws ] ws ≈ zs
  {-# ATP definition P₂ #-}

  postulate h₂ : ∀ {zs} → P₂ zs → ∃[ z' ] ∃[ zs' ] P₂ zs' ∧ zs ≡ z' ∷ zs'
  {-# ATP prove h₂ #-}

lengthStream : ∀ {xs} → Stream xs → length xs ≈N ∞
lengthStream {xs} Sxs = ≈N-coind R h₁ h₂
  where
  R : D → D → Set
  R m n = ∃[ xs ] Stream xs ∧ m ≡ length xs ∧ n ≡ ∞
  {-# ATP definition R #-}

  postulate
    h₁ : ∀ {m n} → R m n →
         m ≡ zero ∧ n ≡ zero ∨
         (∃[ m' ] ∃[ n' ] R m' n' ∧ m ≡ succ₁ m' ∧ n ≡ succ₁ n')
  {-# ATP prove h₁ #-}

  postulate h₂ : R (length xs) ∞
  {-# ATP prove h₂ #-}
