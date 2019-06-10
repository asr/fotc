------------------------------------------------------------------------------
-- Totality properties respect to OrdList (flatten-OrdList-helper)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.SortList.Properties.Totality.OrdList.Flatten where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.Type
open import Interactive.FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- See the combined proof.
postulate
  flatten-OrdList-helper : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                           OrdTree (node t₁ i t₂) →
                           ≤-Lists (flatten t₁) (flatten t₂)
