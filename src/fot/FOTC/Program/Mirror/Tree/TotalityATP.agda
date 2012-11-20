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
mirror-Tree Tt = Tree-ind {A} {B} ihA B[] ihB Tt
  where
  A : D → Set
  A t = Tree (mirror · t)
  {-# ATP definition A #-}

  B : D → Set
  B ts = Forest (map mirror ts)
  {-# ATP definition B #-}

  ihA : ∀ d {ts} → Forest ts → B ts → A (node d ts)
  ihA d {ts} Fts Bts = prf
    where postulate prf : Tree (mirror · node d ts)
          {-# ATP prove prf reverse-Forest #-}

  postulate B[] : Forest (map mirror [])
  {-# ATP prove B[] #-}

  ihB : ∀ {t ts} → Tree t → A t → Forest ts → B ts → B (t ∷ ts)
  ihB {t} {ts} Tt At Fts Bts = prf
    where postulate prf : Forest (map mirror (t ∷ ts))
          {-# ATP prove prf #-}
