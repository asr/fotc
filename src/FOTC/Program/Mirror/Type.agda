------------------------------------------------------------------------------
-- The types used by the mirror function
------------------------------------------------------------------------------

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

{-# ATP axiom nilF #-}
{-# ATP axiom consF #-}
{-# ATP axiom treeT #-}

------------------------------------------------------------------------------
-- From Coq'Art: These induction principles *not cover* the mutual
-- structure of the types Tree and Rose (p. 401).

-- Induction principle for Tree.
indTree : (P : D → Set) →
          (∀ d {ts} → Forest ts → P (node d ts)) →
          ∀ {t} → Tree t → P t
indTree P h (treeT d Fts) = h d Fts

-- Induction principle for Forest.
indForest : (P : D → Set) →
            P [] →
            (∀ {t ts} → Tree t → Forest ts → P ts → P (t ∷ ts)) →
            ∀ {ts} → Forest ts → P ts
indForest P P[] h nilF            = P[]
indForest P P[] h (consF Tt Fts) = h Tt Fts (indForest P P[] h Fts)

------------------------------------------------------------------------------
-- Mutual induction for Tree and Forest

-- Adapted from the induction principles generate from the Coq 8.3 command
-- Scheme Tree_mutual_ind :=
--   Minimality for Tree Sort Prop
-- with Forest_mutual_ind :=
--   Minimality for Forest Sort Prop.

mutual
  mutualIndTree :
    {P Q : D → Set} →
    (∀ d {ts} → Forest ts → Q ts → P (node d ts)) →
    Q [] →
    (∀ {t ts} → Tree t → P t → Forest ts → Q ts → Q (t ∷ ts)) →
    ∀ {t} → Tree t → P t
  mutualIndTree ihP Q[] _   (treeT d nilF)           = ihP d nilF Q[]
  mutualIndTree ihP Q[] ihQ (treeT d (consF Tt Fts)) =
    ihP d (consF Tt Fts) (ihQ Tt (mutualIndTree ihP Q[] ihQ Tt)
                              Fts (mutualIndForest ihP Q[] ihQ Fts))

  mutualIndForest :
     {P Q : D → Set} →
     (∀ d {ts} → Forest ts → Q ts → P (node d ts)) →
     Q [] →
     (∀ {t ts} → Tree t → P t → Forest ts → Q ts → Q (t ∷ ts)) →
     ∀ {ts} → Forest ts → Q ts
  mutualIndForest _   Q[] _   nilF           = Q[]
  mutualIndForest ihP Q[] ihQ (consF Tt Fts) =
    ihQ Tt (mutualIndTree ihP Q[] ihQ Tt) Fts
        (mutualIndForest ihP Q[] ihQ Fts)
