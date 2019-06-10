------------------------------------------------------------------------------
-- Properties for the bisimilarity relation
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Relation.Binary.Bisimilarity.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.Stream.Type
open import Combined.FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, the
-- bisimilarity relation _≈_ on unbounded lists is also a pre-fixed
-- point of the bisimulation functional (see
-- Combined.FOTC.Relation.Binary.Bisimulation).

-- See Issue https://github.com/asr/apia/issues/81 .
≈-inB : D → D → Set
≈-inB xs ys = ∃[ x' ]  ∃[ xs' ] ∃[ ys' ]
                xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys'
{-# ATP definition ≈-inB #-}

≈-in : ∀ {xs ys} →
       ∃[ x' ]  ∃[ xs' ] ∃[ ys' ]
         xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys' →
       xs ≈ ys
≈-in h = ≈-coind ≈-inB h' h
  where
  postulate
    h' : ∀ {xs} {ys} → ≈-inB xs ys →
         ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ ≈-inB xs' ys'
  {-# ATP prove h' #-}

-- See Issue https://github.com/asr/apia/issues/81 .
≈-reflB : D → D → Set
≈-reflB xs ys = xs ≡ ys ∧ Stream xs
{-# ATP definition ≈-reflB #-}

≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
≈-refl {xs} Sxs = ≈-coind ≈-reflB h₁ h₂
  where
  postulate
    h₁ : ∀ {xs ys} → ≈-reflB xs ys →
         ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ ≈-reflB xs' ys'
  {-# ATP prove h₁ #-}

  postulate h₂ : ≈-reflB xs xs
  {-# ATP prove h₂ #-}

-- See Issue https://github.com/asr/apia/issues/81 .
≈-symB : D → D → Set
≈-symB xs ys = ys ≈ xs
{-# ATP definition ≈-symB #-}

≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind ≈-symB h₁ h₂
  where
  postulate
    h₁ : ∀ {ys} {xs} → ≈-symB ys xs →
         ∃[ y' ] ∃[ ys' ] ∃[ xs' ] ys ≡ y' ∷ ys' ∧ xs ≡ y' ∷ xs' ∧ ≈-symB ys' xs'
  {-# ATP prove h₁ #-}

  postulate h₂ : ≈-symB ys xs
  {-# ATP prove h₂ #-}

-- See Issue https://github.com/asr/apia/issues/81 .
≈-transB : D → D → Set
≈-transB xs zs = ∃[ ys ] xs ≈ ys ∧ ys ≈ zs
{-# ATP definition ≈-transB #-}

≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind ≈-transB h₁ h₂
  where
  postulate
    h₁ : ∀ {as} {cs} → ≈-transB as cs →
         ∃[ a' ] ∃[ as' ] ∃[ cs' ] as ≡ a' ∷ as' ∧ cs ≡ a' ∷ cs' ∧ ≈-transB as' cs'
  {-# ATP prove h₁ #-}

  postulate h₂ : ≈-transB xs zs
  {-# ATP prove h₂ #-}

postulate ∷-injective≈ : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
{-# ATP prove ∷-injective≈ #-}

postulate ∷-rightCong≈ : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
{-# ATP prove ∷-rightCong≈ ≈-in #-}
