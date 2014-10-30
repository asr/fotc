------------------------------------------------------------------------------
-- First-order logic with equality
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module exported all the logical constants and the
-- propositional equality. This module is re-exported by the "base"
-- modules whose theories are defined on first-order logic + equality.

module Common.FOL.FOL-Eq where

-- First-order logic (without equality).
open import Common.FOL.FOL public

-- Propositional equality.
open import Common.FOL.Relation.Binary.PropositionalEquality public
