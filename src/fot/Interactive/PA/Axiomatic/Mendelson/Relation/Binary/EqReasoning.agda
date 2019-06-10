------------------------------------------------------------------------------
-- Equality reasoning on axiomatic PA
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module only re-export the preorder reasoning instanced on
-- the axiomatic PA propositional equality.

module Interactive.PA.Axiomatic.Mendelson.Relation.Binary.EqReasoning where

open import Interactive.PA.Axiomatic.Mendelson.Base
open import Interactive.PA.Axiomatic.Mendelson.Relation.Binary.PropositionalEquality
  using ( ≈-refl ; ≈-trans)

import Common.Relation.Binary.PreorderReasoning
open module ≈-Reasoning =
  Common.Relation.Binary.PreorderReasoning _≈_ ≈-refl ≈-trans public
    renaming ( _∼⟨_⟩_ to _≈⟨_⟩_ )
