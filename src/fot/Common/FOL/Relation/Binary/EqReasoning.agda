------------------------------------------------------------------------------
-- Equality reasoning on FOL
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module only re-export the preorder reasoning instanced on the
-- propositional equality.

module Common.FOL.Relation.Binary.EqReasoning where

open import Common.FOL.FOL-Eq using ( _≡_ ; refl ; trans )

import Common.Relation.Binary.PreorderReasoning
open module ≡-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≡_ refl trans public
    renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )
