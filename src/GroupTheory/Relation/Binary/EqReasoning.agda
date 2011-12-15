------------------------------------------------------------------------------
-- Equality reasoning on group theory
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module only re-export the preorder reasoning instanced on
-- the group theory propositional equality.

module GroupTheory.Relation.Binary.EqReasoning where

open import GroupTheory.Base

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≡_ refl trans public
    renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )
