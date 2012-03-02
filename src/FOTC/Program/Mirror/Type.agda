------------------------------------------------------------------------------
-- The types used by the mirror function
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Mirror.Type where

open import FOTC.Base
open import FOTC.Data.List

------------------------------------------------------------------------------
-- Tree terms.
postulate
  node : D → D → D

mutual
  -- The list of rose trees (called forest).
  data Forest : D → Set where
    nilF  :                                 Forest []
    consF : ∀ {t ts} → Tree t → Forest ts → Forest (t ∷ ts)

  -- The rose tree type.
  data Tree : D → Set where
    treeT : ∀ d {ts} → Forest ts → Tree (node d ts)

{-# ATP axiom nilF consF treeT #-}

------------------------------------------------------------------------------
-- From Coq'Art: These induction principles *not cover* the mutual
-- structure of the types Tree and Rose (p. 401).

-- Induction principle for Tree.
indTree : (A : D → Set) →
          (∀ d {ts} → Forest ts → A (node d ts)) →
          ∀ {t} → Tree t → A t
indTree A h (treeT d Fts) = h d Fts

-- Induction principle for Forest.
indForest : (A : D → Set) →
            A [] →
            (∀ {t ts} → Tree t → Forest ts → A ts → A (t ∷ ts)) →
            ∀ {ts} → Forest ts → A ts
indForest A A[] h nilF            = A[]
indForest A A[] h (consF Tt Fts) = h Tt Fts (indForest A A[] h Fts)

------------------------------------------------------------------------------
-- Mutual induction for Tree and Forest

-- Adapted from the induction principles generate from the Coq 8.3 command
-- Scheme Tree_mutual_ind :=
--   Minimality for Tree Sort Prop
-- with Forest_mutual_ind :=
--   Minimality for Forest Sort Prop.

mutual
  mutualIndTree :
    {A B : D → Set} →
    (∀ d {ts} → Forest ts → B ts → A (node d ts)) →
    B [] →
    (∀ {t ts} → Tree t → A t → Forest ts → B ts → B (t ∷ ts)) →
    ∀ {t} → Tree t → A t
  mutualIndTree ihA B[] _   (treeT d nilF)           = ihA d nilF B[]
  mutualIndTree ihA B[] ihB (treeT d (consF Tt Fts)) =
    ihA d (consF Tt Fts) (ihB Tt (mutualIndTree ihA B[] ihB Tt)
                              Fts (mutualIndForest ihA B[] ihB Fts))

  mutualIndForest :
     {P B : D → Set} →
     (∀ d {ts} → Forest ts → B ts → P (node d ts)) →
     B [] →
     (∀ {t ts} → Tree t → P t → Forest ts → B ts → B (t ∷ ts)) →
     ∀ {ts} → Forest ts → B ts
  mutualIndForest _   B[] _   nilF           = B[]
  mutualIndForest ihP B[] ihB (consF Tt Fts) =
    ihB Tt (mutualIndTree ihP B[] ihB Tt) Fts
        (mutualIndForest ihP B[] ihB Fts)
