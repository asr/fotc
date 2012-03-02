------------------------------------------------------------------------------
-- FOL with equality
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module exported all the logical constants and the
-- propositional equality. This module is re-exported by the "base"
-- modules whose theories are defined on FOL + equality.

module Common.FOL.FOL-Eq where

-- FOL (without equality).
open import Common.FOL.FOL public

-- The propositional equality.
import Common.FOL.Relation.Binary.PropositionalEquality
open module Eq =
  Common.FOL.Relation.Binary.PropositionalEquality.Inductive public
