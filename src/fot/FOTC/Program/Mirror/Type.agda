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
postulate node : D → D → D

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
-- using the command (see Coq'Art p. 401).
--
-- Scheme Tree_mutual_ind :=
--   Minimality for Tree Sort Prop
-- with Forest_mutual_ind :=
--   Minimality for Forest Sort Prop.

Tree-mutual-ind :
  {A B : D → Set} →
  (∀ d {ts} → Forest ts → B ts → A (node d ts)) →
  B [] →
  (∀ {t ts} → Tree t → A t → Forest ts → B ts → B (t ∷ ts)) →
  ∀ {t} → Tree t → A t

Forest-mutual-ind :
  {A B : D → Set} →
  (∀ d {ts} → Forest ts → B ts → A (node d ts)) →
  B [] →
  (∀ {t ts} → Tree t → A t → Forest ts → B ts → B (t ∷ ts)) →
  ∀ {ts} → Forest ts → B ts

Tree-mutual-ind ihA B[] _   (tree d fnil)           = ihA d fnil B[]
Tree-mutual-ind ihA B[] ihB (tree d (fcons Tt Fts)) =
  ihA d (fcons Tt Fts) (ihB Tt (Tree-mutual-ind ihA B[] ihB Tt)
                            Fts (Forest-mutual-ind ihA B[] ihB Fts))

Forest-mutual-ind _   B[] _   fnil           = B[]
Forest-mutual-ind ihA B[] ihB (fcons Tt Fts) =
  ihB Tt (Tree-mutual-ind ihA B[] ihB Tt) Fts
      (Forest-mutual-ind ihA B[] ihB Fts)
