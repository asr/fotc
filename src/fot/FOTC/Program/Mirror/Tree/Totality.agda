------------------------------------------------------------------------------
-- Totality properties respect to Tree
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Mirror.Tree.Totality where

open import FOTC.Base
open FOTC.Base.BList
open import FOTC.Data.List
open import FOTC.Program.Mirror.Forest.Totality
open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
mirror-Tree Tt = Tree-ind {A} {B} ihA B[] ihB Tt
  where
  A : D → Set
  A t = Tree (mirror · t)

  B : D → Set
  B ts = Forest (map mirror ts)

  ihA : ∀ d {ts} → Forest ts → B ts → A (node d ts)
  ihA d {ts} Fts Bts = subst Tree
                             (sym (mirror-eq d ts))
                             (tree d (reverse-Forest Bts))

  B[] : Forest (map mirror [])
  B[] = subst Forest (sym (map-[] mirror)) fnil

  ihB : ∀ {t ts} → Tree t → A t → Forest ts → B ts → B (t ∷ ts)
  ihB {t} {ts} Tt At Fts Bts =
    subst Forest (sym (map-∷ mirror t ts)) (fcons At Bts)
