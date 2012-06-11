------------------------------------------------------------------------------
-- The map-iterate property using the standard library
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of the standard library on
-- 11 June 2012.

-- From: Nils Anders Danielsson and Thorsten Altenkirch. Mixing
-- Induction and Coinduction. Draft 2009.

module MapIterateSL where

open import Coinduction

open import Data.Stream

------------------------------------------------------------------------------

map-iterate : ∀ {A} (f : A → A) (x : A) →
              map f (iterate f x) ≈ iterate f (f x)
map-iterate f x = f x ∷ ♯ map-iterate f (f x)
