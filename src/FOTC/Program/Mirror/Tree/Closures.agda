------------------------------------------------------------------------------
-- Properties related with the closures of the rose tree type
------------------------------------------------------------------------------

module FOTC.Program.Mirror.Tree.Closures where

open import FOTC.Base

open import FOTC.Data.List

open import FOTC.Program.Mirror.Forest.Closures
open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
mirror-Tree Tt = mutualIndTree {P} {Q} ihP Q[] ihQ Tt
  where
    P : D → Set
    P t = Tree (mirror · t)

    Q : D → Set
    Q ts = Forest (map mirror ts)

    ihP : ∀ d {ts} → Forest ts → Q ts → P (node d ts)
    ihP d {ts} Fts Qts = subst Tree
                               (sym (mirror-eq d ts))
                               (treeT d (reverse-Forest Qts))

    Q[] : Forest (map mirror [])
    Q[] = subst Forest (sym (map-[] mirror)) nilF

    ihQ : {t ts : D} → Tree t → P t → Forest ts → Q ts → Q (t ∷ ts)
    ihQ {t} {ts} Tt Pt Fts Qts =
      subst Forest (sym (map-∷ mirror t ts)) (consF Pt Qts)
