------------------------------------------------------------------------------
-- Totality properties for Tree using induction instance
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Program.Mirror.Tree.Induction.Instances.TotalityATP where

open import FOTC.Base
open import FOTC.Base.List
open import FOTC.Data.List
open import FOTC.Program.Mirror.Forest.TotalityATP
open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.Type

------------------------------------------------------------------------------

mirror-Tree-ind-instance :
  (∀ d {ts} → Forest ts → Forest (map mirror ts) → Tree (mirror · node d ts)) →
  Forest (map mirror []) →
  (∀ {t ts} → Tree t → Tree (mirror · t) → Forest ts →
    Forest (map mirror ts) → Forest (map mirror (t ∷ ts))) →
  ∀ {t} → Tree t → Tree (mirror · t)
mirror-Tree-ind-instance = Tree-mutual-ind

postulate mirror-Tree : ∀ {t} → Tree t → Tree (mirror · t)
{-# ATP prove mirror-Tree mirror-Tree-ind-instance reverse-Forest #-}
