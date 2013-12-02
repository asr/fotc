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
≈-pre-fixed {xs} {ys} h = ≈-coind (λ zs _ → zs ≡ zs) h' refl
  where
  postulate
    h' : xs ≡ xs →
         ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≡ xs'
  {-# ATP prove h' #-}

≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
≈-refl {xs} Sxs = ≈-coind (λ ys _ → ys ≡ ys) h refl
  where
  postulate
    h : xs ≡ xs →
        ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ xs ≡ x' ∷ ys' ∧ xs' ≡ xs'
  {-# ATP prove h #-}

≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind (λ zs _ → zs ≡ zs) h refl
  where
  postulate
    h : ys ≡ ys →
        ∃[ y' ] ∃[ ys' ] ∃[ xs' ] ys ≡ y' ∷ ys' ∧ xs ≡ y' ∷ xs' ∧ ys' ≡ ys'
  {-# ATP prove h #-}

≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind (λ ws _ → ws ≡ ws) h refl
  where
  postulate
    h : xs ≡ xs →
        ∃[ x' ] ∃[ xs' ] ∃[ zs' ] xs ≡ x' ∷ xs' ∧ zs ≡ x' ∷ zs' ∧ xs' ≡ xs'
  {-# ATP prove h #-}

postulate ∷-injective≈ : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
{-# ATP prove ∷-injective≈ #-}

postulate ∷-rightCong≈ : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
{-# ATP prove ∷-rightCong≈ ≈-pre-fixed #-}
