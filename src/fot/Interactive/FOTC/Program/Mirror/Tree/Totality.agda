------------------------------------------------------------------------------
-- Totality properties for Tree
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Program.Mirror.Tree.Totality where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Program.Mirror.Forest.Totality
open import Interactive.FOTC.Program.Mirror.Mirror
open import Interactive.FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
mirror-Tree = Tree-mutual-ind {A} {B} hA B[] hB
  where
  A : D → Set
  A t = Tree (mirror · t)

  B : D → Set
  B ts = Forest (map mirror ts)

  hA : ∀ d {ts} → Forest ts → B ts → A (node d ts)
  hA d {ts} Fts Bts = subst Tree
                            (sym (mirror-eq d ts))
                            (tree d (reverse-Forest Bts))

  B[] : B []
  B[] = subst Forest (sym (map-[] mirror)) fnil

  hB : ∀ {t ts} → Tree t → A t → Forest ts → B ts → B (t ∷ ts)
  hB {t} {ts} Tt At Fts Bts =
    subst Forest (sym (map-∷ mirror t ts)) (fcons At Bts)
