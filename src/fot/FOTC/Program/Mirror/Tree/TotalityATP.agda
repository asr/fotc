------------------------------------------------------------------------------
-- Totality properties for Tree
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Mirror.Tree.TotalityATP where

open import FOTC.Base
open FOTC.Base.BList
open import FOTC.Data.List
open import FOTC.Program.Mirror.Forest.TotalityATP
open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
mirror-Tree = Tree-mutual-ind {A} {B} ihA B[] ihB
  where
  A : D → Set
  A t = Tree (mirror · t)
  {-# ATP definition A #-}

  B : D → Set
  B ts = Forest (map mirror ts)
  {-# ATP definition B #-}

  postulate ihA : ∀ d {ts} → Forest ts → B ts → A (node d ts)
  {-# ATP prove ihA reverse-Forest #-}

  postulate B[] : B []
  {-# ATP prove B[] #-}

  postulate ihB : ∀ {t ts} → Tree t → A t → Forest ts → B ts → B (t ∷ ts)
  {-# ATP prove ihB #-}
