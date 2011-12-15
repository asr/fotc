------------------------------------------------------------------------------
-- Equality reasoning on FOTC
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module only re-export the preorder reasoning instanced on the
-- FOTC propositional equality.

module FOTC.Relation.Binary.EqReasoning where

open import FOTC.Base

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≡_ refl trans public
    renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )
