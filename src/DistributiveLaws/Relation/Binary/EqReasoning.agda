------------------------------------------------------------------------------
-- Equality reasoning for the distributive laws
------------------------------------------------------------------------------

-- This module only re-export the preorder reasoning instanced on
-- the distributive laws propositional equality.

module DistributiveLaws.Relation.Binary.EqReasoning where

open import DistributiveLaws.Base

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≡_ refl trans public
    renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )
