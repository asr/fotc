------------------------------------------------------------------------------
-- Properties related with the closures of the tree type
------------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

module FOTC.Program.Mirror.Tree.ClosuresATP where

open import FOTC.Base

open import FOTC.Data.List

open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.ListTree.Closures
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
mirror-Tree (treeT d nilLT) = prf
  where
    postulate prf : Tree (mirror · node d [])
    {-# ATP prove prf #-}

mirror-Tree (treeT d (consLT {t} {ts} Tt LTts)) =
  subst Tree (sym (mirror-eq d (t ∷ ts))) (treeT d helper)

  where
    helper : ListTree (reverse (map mirror (t ∷ ts)))
    helper = reverse-ListTree (map-ListTree mirror mirror-Tree (consLT Tt LTts))
