------------------------------------------------------------------------------
-- Equality reasoning for the distributive laws
------------------------------------------------------------------------------

-- This module only re-export the equational reasoning instanced on
-- the distributive laws propositional equality.

module DistributiveLaws.Relation.Binary.EqReasoning where

open import DistributiveLaws.Base

import Common.Relation.Binary.EqReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.EqReasoning _≡_ refl trans public
