------------------------------------------------------------------------------
-- Equality reasoning on inductive PA
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module only re-export the preorder reasoning instanced on
-- the inductive PA propositional equality.

module Combined.PA.Inductive.Relation.Binary.EqReasoning where

open import Combined.PA.Inductive.Base

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≡_ refl trans public
    renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )
