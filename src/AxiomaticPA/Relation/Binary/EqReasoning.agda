------------------------------------------------------------------------------
-- Equality reasoning on PA
------------------------------------------------------------------------------

-- This module only re-export the preorder reasoning instanced on
-- the PA propositional equality.

module AxiomaticPA.Relation.Binary.EqReasoning where

open import AxiomaticPA.Base
open import AxiomaticPA.Relation.Binary.PropositionalEqualityI
  using ( refl ; trans)

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≣_ refl trans public
    renaming ( _∼⟨_⟩_ to _≣⟨_⟩_ )
