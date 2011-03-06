------------------------------------------------------------------------------
-- Properties related with the closures of the rose tree type
------------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

module FOTC.Program.Mirror.Tree.ClosuresATP where

open import FOTC.Base

open import FOTC.Data.List

open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.Forest.Closures
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
mirror-Tree (treeT d nilF) = prf
  where
    postulate prf : Tree (mirror · node d [])
    {-# ATP prove prf #-}

mirror-Tree (treeT d (consF {t} {ts} Tt Fts)) =
  subst Tree (sym (mirror-eq d (t ∷ ts))) (treeT d helper)

  where
    helper : Forest (reverse (map mirror (t ∷ ts)))
    helper = reverse-Forest (map-Forest mirror mirror-Tree (consF Tt Fts))
