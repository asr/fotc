-- Tested with FOT and agda2atp on 08 December 2011.

module Bottom where

open import Common.Universe
open import Common.Data.Empty
import Common.Relation.Binary.PropositionalEquality
open module Eq =
  Common.Relation.Binary.PropositionalEquality.Inductive

postulate bot : ⊥

postulate
  zero : D
  succ : D → D

postulate false : zero ≡ succ zero
{-# ATP prove false bot #-}

-- $ agda2atp -isrc -inotes/papers/FoSSaCS-2012/  notes/papers/FoSSaCS-2012/Bottom.agda
-- Proving the conjecture in /tmp/Bottom.false_17.tptp ...
-- Vampire 0.6 (revision 903) proved the conjecture in /tmp/Bottom.false_17.tptp
