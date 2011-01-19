------------------------------------------------------------------------------
-- Equality reasoning on LTC
------------------------------------------------------------------------------

-- This module only re-export the preorder reasoning instanced on the
-- LTC propositional equality.

module LTC.Relation.Binary.EqReasoning where

open import LTC.Base

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≡_ refl trans public
    renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )
