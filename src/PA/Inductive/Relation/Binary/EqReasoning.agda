------------------------------------------------------------------------------
-- Equality reasoning on inductive PA
------------------------------------------------------------------------------

-- This module only re-export the preorder reasoning instanced on
-- the inductive PA propositional equality.

module PA.Inductive.Relation.Binary.EqReasoning where

open import PA.Inductive.Base

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≡_ refl trans public
    renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )
