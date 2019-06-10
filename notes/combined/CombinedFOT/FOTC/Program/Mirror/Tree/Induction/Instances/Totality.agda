------------------------------------------------------------------------------
-- Totality properties for Tree using induction instance
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombinedFOT.FOTC.Program.Mirror.Tree.Induction.Instances.Totality where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.List
open import Combined.FOTC.Data.List
open import Combined.FOTC.Program.Mirror.Forest.Totality
open import Combined.FOTC.Program.Mirror.Mirror
open import Combined.FOTC.Program.Mirror.Type

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
