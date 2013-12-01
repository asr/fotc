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
-- Because a greatest post-fixed point is a fixed-point, the
-- bisimilarity relation _≈_ on unbounded lists is also a pre-fixed
-- point of the bisimulation functional (see
-- FOTC.Relation.Binary.Bisimulation).
≈-pre-fixed : ∀ {xs ys} →
              (∃[ x' ]  ∃[ xs' ] ∃[ ys' ]
                xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys') →
              xs ≈ ys
≈-pre-fixed {xs} {ys} h = ≈-coind B h' refl
  where
  B : D → D → Set
  B xs ys = xs ≡ xs
  {-# ATP definition B #-}

  postulate
    h' : B xs ys →
         ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys'
  {-# ATP prove h' #-}

≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
≈-refl {xs} Sxs = ≈-coind B h refl
  where
  B : D → D → Set
  B xs ys = xs ≡ xs
  {-# ATP definition B #-}

  postulate
    h : B xs xs →
        ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ xs ≡ x' ∷ ys' ∧ B xs' xs'
  {-# ATP prove h #-}

≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind B h refl
  where
  B : D → D → Set
  B xs ys = xs ≡ xs
  {-# ATP definition B #-}

  postulate
    h : B ys xs →
        ∃[ y' ] ∃[ ys' ] ∃[ xs' ] ys ≡ y' ∷ ys' ∧ xs ≡ y' ∷ xs' ∧ B ys' xs'
  {-# ATP prove h #-}

≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind B h refl
  where
  B : D → D → Set
  B xs zs = xs ≡ xs
  {-# ATP definition B #-}

  postulate
    h : B xs zs →
        ∃[ x' ] ∃[ xs' ] ∃[ zs' ] xs ≡ x' ∷ xs' ∧ zs ≡ x' ∷ zs' ∧ B xs' zs'
  {-# ATP prove h #-}

postulate ∷-injective≈ : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
{-# ATP prove ∷-injective≈ #-}

postulate ∷-rightCong≈ : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
{-# ATP prove ∷-rightCong≈ ≈-pre-fixed #-}
