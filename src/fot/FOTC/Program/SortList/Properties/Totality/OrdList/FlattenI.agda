------------------------------------------------------------------------------
-- Totality properties respect to OrdList (flatten-OrdList-helper)
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.SortList.Properties.Totality.OrdList.FlattenI where

open import FOTC.Base
open import FOTC.Data.Nat.Type
open import FOTC.Program.SortList.SortList

------------------------------------------------------------------------------
-- See the combined proof.
postulate
  flatten-OrdList-helper : ∀ {t₁ i t₂} → Tree t₁ → N i → Tree t₂ →
                           OrdTree (node t₁ i t₂) →
                           ≤-Lists (flatten t₁) (flatten t₂)
