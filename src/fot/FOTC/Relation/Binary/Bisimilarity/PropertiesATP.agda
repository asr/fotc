------------------------------------------------------------------------------
-- Properties for the bisimilarity relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Relation.Binary.Bisimilarity.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream
open import FOTC.Relation.Binary.Bisimilarity

------------------------------------------------------------------------------

≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
≈-refl {xs} Sxs = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R xs ys = Stream xs ∧ xs ≡ ys
  {-# ATP definition R #-}

  postulate h₁ : ∀ {xs ys} → R xs ys → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
                 R xs' ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'
  {-# ATP prove h₁ #-}

  postulate h₂ : R xs xs
  {-# ATP prove h₂ #-}

≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R xs ys = ys ≈ xs
  {-# ATP definition R #-}

  postulate h₁ : ∀ {xs ys} → R xs ys →
                 ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
                 R xs' ys' ∧ xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys'
  {-# ATP prove h₁ #-}

  postulate h₂ : R ys xs
  {-# ATP prove h₂ #-}

≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind R h₁ h₂
  where
  R : D → D → Set
  R xs zs = ∃[ ys ] xs ≈ ys ∧ ys ≈ zs
  {-# ATP definition R #-}

  postulate h₁ : ∀ {xs zs} → R xs zs →
                 ∃[ x' ] ∃[ xs' ] ∃[ zs' ]
                 R xs' zs' ∧ xs ≡ x' ∷ xs' ∧ zs ≡ x' ∷ zs'

  postulate h₂ : R xs zs
  {-# ATP prove h₂ #-}

postulate ∷-injective≈ : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
{-# ATP prove ∷-injective≈ #-}

postulate ∷-rightCong≈ : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
{-# ATP prove ∷-rightCong≈ ≈-pre-fixed #-}
