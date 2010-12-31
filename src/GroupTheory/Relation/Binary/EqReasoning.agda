------------------------------------------------------------------------------
-- Equality reasoning on group theory
------------------------------------------------------------------------------

-- This module only re-export the equational reasoning instanced on
-- the group theory propositional equality.

module GroupTheory.Relation.Binary.EqReasoning where

open import GroupTheory.Base

import Common.Relation.Binary.EqReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.EqReasoning _≡_ refl trans public
