------------------------------------------------------------------------------
-- Properties for the bisimilarity relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Relation.Binary.Bisimilarity.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.Stream.Type
open import FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, the
-- bisimilarity relation _≈_ on unbounded lists is also a pre-fixed
-- point of the bisimulation functional (see
-- FOTC.Relation.Binary.Bisimulation).
≈-pre-fixed : (∀ {xs ys} → ∃[ x' ]  ∃[ xs' ] ∃[ ys' ]
                xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≈ ys') →
              ∀ {xs ys} → xs ≈ ys
≈-pre-fixed h = ≈-coind (λ zs _ → zs ≡ zs) h' refl
  where
  postulate
    h' : ∀ {xs} {ys} → xs ≡ xs →
         ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ xs' ≡ xs'
  -- TODO (23 December 2013): The translation failed because we do not
  -- know how erase a term.
  -- {-# ATP prove h' #-}

≈-refl : ∀ {xs} → Stream xs → xs ≈ xs
≈-refl {xs} Sxs = ≈-coind B h₁ h₂
  where
  B : D → D → Set
  B xs ys = xs ≡ ys ∧ Stream xs
  {-# ATP definition B #-}

  postulate
    h₁ : ∀ {xs ys} → B xs ys →
         ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys'
  {-# ATP prove h₁ #-}

  postulate h₂ : B xs xs
  {-# ATP prove h₂ #-}

≈-sym : ∀ {xs ys} → xs ≈ ys → ys ≈ xs
≈-sym {xs} {ys} xs≈ys = ≈-coind B h₁ h₂
  where
  B : D → D → Set
  B xs ys = ys ≈ xs
  {-# ATP definition B #-}

  postulate
    h₁ : ∀ {ys} {xs} → B ys xs →
         ∃[ y' ] ∃[ ys' ] ∃[ xs' ] ys ≡ y' ∷ ys' ∧ xs ≡ y' ∷ xs' ∧ B ys' xs'
  {-# ATP prove h₁ #-}

  postulate h₂ : B ys xs
  {-# ATP prove h₂ #-}

≈-trans : ∀ {xs ys zs} → xs ≈ ys → ys ≈ zs → xs ≈ zs
≈-trans {xs} {ys} {zs} xs≈ys ys≈zs = ≈-coind B h₁ h₂
  where
  B : D → D → Set
  B xs zs = ∃[ ys ] xs ≈ ys ∧ ys ≈ zs
  {-# ATP definition B #-}

  postulate
    h₁ : ∀ {as} {cs} → B as cs →
         ∃[ a' ] ∃[ as' ] ∃[ cs' ] as ≡ a' ∷ as' ∧ cs ≡ a' ∷ cs' ∧ B as' cs'
  {-# ATP prove h₁ #-}

  postulate h₂ : B xs zs
  {-# ATP prove h₂ #-}

postulate ∷-injective≈ : ∀ {x xs ys} → x ∷ xs ≈ x ∷ ys → xs ≈ ys
{-# ATP prove ∷-injective≈ #-}

-- TODO (23 December 2013).
-- postulate ∷-rightCong≈ : ∀ {x xs ys} → xs ≈ ys → x ∷ xs ≈ x ∷ ys
-- {-# ATP prove ∷-rightCong≈ ≈-pre-fixed #-}
