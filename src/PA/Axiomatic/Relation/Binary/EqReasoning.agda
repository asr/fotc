------------------------------------------------------------------------------
-- Equality reasoning on axiomatic PA
------------------------------------------------------------------------------

-- This module only re-export the preorder reasoning instanced on
-- the axiomatic PA propositional equality.

module PA.Axiomatic.Relation.Binary.EqReasoning where

open import PA.Axiomatic.Base
open import PA.Axiomatic.Relation.Binary.PropositionalEqualityI
  using ( refl ; trans)

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≣_ refl trans public
    renaming ( _∼⟨_⟩_ to _≣⟨_⟩_ )
