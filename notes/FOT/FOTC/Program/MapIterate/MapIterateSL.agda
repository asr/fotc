------------------------------------------------------------------------------
-- The map-iterate property using the standard library
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From: Nils Anders Danielsson and Thorsten Altenkirch. Mixing
-- Induction and Coinduction. Draft 2009.

module FOT.FOTC.Program.MapIterate.MapIterateSL where

open import Coinduction
open import Data.Stream
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

map-iterate : ∀ {A} (f : A → A) (x : A) →
              map f (iterate f x) ≈ iterate f (f x)
map-iterate f x = f x ∷ ♯ map-iterate f (f x)
