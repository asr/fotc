------------------------------------------------------------------------------
-- Equality reasoning on axiomatic PA
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module only re-export the preorder reasoning instanced on
-- the axiomatic PA propositional equality.

module PA.Axiomatic.Standard.Relation.Binary.EqReasoning where

open import PA.Axiomatic.Standard.Base

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≡_ refl trans public
    renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )
