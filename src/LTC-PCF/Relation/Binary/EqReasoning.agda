------------------------------------------------------------------------------
-- Equality reasoning on LTC-PCF
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module only re-export the preorder reasoning instanced on the
-- LTC-PCF (FOTC) propositional equality.

module LTC-PCF.Relation.Binary.EqReasoning where

open import LTC-PCF.Base

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≡_ refl trans public
    renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )
