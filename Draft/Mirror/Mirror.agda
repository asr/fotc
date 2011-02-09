------------------------------------------------------------------------------
-- The mirror function
------------------------------------------------------------------------------

module Draft.Mirror.Mirror where

open import LTC.Base

open import LTC.Data.List

------------------------------------------------------------------------------

-- Tree terms.
postulate
  node : D → D → D

mutual
  -- The lists of trees type.
  data ListTree : D → Set where
    nilLT  : ListTree []
    consLT : ∀ {t ts} → Tree t → ListTree ts → ListTree (t ∷ ts)

  -- The tree type.
  data Tree : D → Set where
    treeT : ∀ d {ts} → ListTree ts → Tree (node d ts)

{-# ATP hint nilLT #-}
{-# ATP hint consLT #-}
{-# ATP hint treeT #-}

-- The mirror function.
postulate
  mirror    : D
  mirror-eq : ∀ d ts → mirror · (node d ts) ≡ node d (reverse (map mirror ts))
{-# ATP axiom mirror-eq #-}
