------------------------------------------------------------------------------
-- Equality reasoning on LTC
------------------------------------------------------------------------------

-- This module only re-export the equational reasoning instanced on
-- the LTC propositional equality.

module LTC.Relation.Binary.EqReasoning where

open import LTC.Base

import Common.Relation.Binary.EqReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.EqReasoning _≡_ refl trans public
