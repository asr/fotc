------------------------------------------------------------------------------
-- Totality properties for Tree
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Mirror.Tree.TotalityATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Program.Mirror.Forest.TotalityATP
open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.Type

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
