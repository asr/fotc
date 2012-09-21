------------------------------------------------------------------------------
-- The types used by the mirror function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Mirror.Type where

open import FOTC.Base
open FOTC.Base.BList
open import FOTC.Data.List

------------------------------------------------------------------------------
-- Tree terms.
postulate
  node : D → D → D

-- The mutually totality predicates

data Forest : D → Set  -- The list of rose trees (called forest).
data Tree   : D → Set  -- The rose tree type.

data Forest where
  fnil  :                                 Forest []
  fcons : ∀ {t ts} → Tree t → Forest ts → Forest (t ∷ ts)
{-# ATP axiom fnil fcons #-}

data Tree where
  tree : ∀ d {ts} → Forest ts → Tree (node d ts)
{-# ATP axiom tree #-}

------------------------------------------------------------------------------
-- Mutual induction for Tree and Forest

-- Adapted from the mutual induction principles generate from Coq 8.4
-- using the command:
--
-- Scheme Tree_mutual_ind :=
--   Minimality for Tree Sort Prop
-- with Forest_mutual_ind :=
--   Minimality for Forest Sort Prop.

Tree-ind :
  {A B : D → Set} →
  (∀ d {ts} → Forest ts → B ts → A (node d ts)) →
  B [] →
  (∀ {t ts} → Tree t → A t → Forest ts → B ts → B (t ∷ ts)) →
  ∀ {t} → Tree t → A t

Forest-ind :
  {P B : D → Set} →
  (∀ d {ts} → Forest ts → B ts → P (node d ts)) →
  B [] →
  (∀ {t ts} → Tree t → P t → Forest ts → B ts → B (t ∷ ts)) →
  ∀ {ts} → Forest ts → B ts

Tree-ind ihA B[] _   (tree d fnil)           = ihA d fnil B[]
Tree-ind ihA B[] ihB (tree d (fcons Tt Fts)) =
  ihA d (fcons Tt Fts) (ihB Tt (Tree-ind ihA B[] ihB Tt)
                              Fts (Forest-ind ihA B[] ihB Fts))

Forest-ind _   B[] _   fnil           = B[]
Forest-ind ihP B[] ihB (fcons Tt Fts) =
  ihB Tt (Tree-ind ihP B[] ihB Tt) Fts (Forest-ind ihP B[] ihB Fts)
