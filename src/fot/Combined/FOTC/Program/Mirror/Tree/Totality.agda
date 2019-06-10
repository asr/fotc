------------------------------------------------------------------------------
-- Totality properties for Tree
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Program.Mirror.Tree.Totality where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.List
open import Combined.FOTC.Program.Mirror.Forest.Totality
open import Combined.FOTC.Program.Mirror.Mirror
open import Combined.FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
mirror-Tree = Tree-mutual-ind {A} {B} hA B[] hB
  where
  A : D → Set
  A t = Tree (mirror · t)
  {-# ATP definition A #-}

  B : D → Set
  B ts = Forest (map mirror ts)
  {-# ATP definition B #-}

  postulate
    hA  : ∀ d {ts} → Forest ts → B ts → A (node d ts)
    B[] : B []
    hB  : ∀ {t ts} → Tree t → A t → Forest ts → B ts → B (t ∷ ts)
  {-# ATP prove hA reverse-Forest #-}
  {-# ATP prove B[] #-}
  {-# ATP prove hB #-}
