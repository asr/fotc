------------------------------------------------------------------------------
-- A stronger (maybe invalid) principle for ≈-coind
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Relation.Binary.Bisimilarity.Type where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- A stronger (maybe invalid) principle for ≈-coind.
postulate
  ≈-stronger-coind :
    ∀ (B : D → D → Set) {xs ys} →
    (B xs ys → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
      xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys') →
    B xs ys → xs ≈ ys
