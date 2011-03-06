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
    nilF  : Forest []
    consF : ∀ {t ts} → Tree t → Forest ts → Forest (t ∷ ts)

  -- The rose tree type.
  data Tree : D → Set where
    treeT : ∀ d {ts} → Forest ts → Tree (node d ts)

{-# ATP hint nilF #-}
{-# ATP hint consF #-}
{-# ATP hint treeT #-}

-- Induction principle for Tree.
indTree : (P : D → Set) →
          (∀ d {ts} → Forest ts → P (node d ts)) →
          ∀ {t} → Tree t → P t
indTree P h (treeT d LTts) = h d LTts

-- Induction principle for Forest.
indForest : (P : D → Set) →
            P [] →
            (∀ {t ts} → Tree t → Forest ts → P ts → P (t ∷ ts)) →
            ∀ {ts} → Forest ts → P ts
indForest P P[] h nilF            = P[]
indForest P P[] h (consF Tt LTts) = h Tt LTts (indForest P P[] h LTts)
