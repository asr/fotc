------------------------------------------------------------------------------
-- A stronger (maybe invalid) principle for ≈-coind
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module InteractiveFOT.FOTC.Relation.Binary.Bisimilarity.Type where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Relation.Binary.Bisimilarity.Type

------------------------------------------------------------------------------
-- A stronger (maybe invalid) principle for ≈-coind.
postulate
  ≈-stronger-coind :
    ∀ (B : D → D → Set) {xs ys} →
    (B xs ys → ∃[ x' ] ∃[ xs' ] ∃[ ys' ]
      xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys') →
    B xs ys → xs ≈ ys
