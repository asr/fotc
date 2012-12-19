------------------------------------------------------------------------------
-- Testing polymorphic lists using postulates
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Polymorphism.ListPostulate where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- "Heterogeneous" lists

postulate
  List : D → Set
  List-in : ∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] List xs' ∧ xs ≡ x' ∷ xs') →
            List xs
  List-ind :
    (A : D → Set) →
    (∀ {xs} → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] A xs' ∧ xs ≡ x' ∷ xs') → A xs) →
    ∀ {xs} → List xs → A xs
