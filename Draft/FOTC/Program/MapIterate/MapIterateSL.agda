------------------------------------------------------------------------------
-- The map-iterate property using the standard library
------------------------------------------------------------------------------

-- Tested with the development version on 12 July 2011.

-- From: Nils Anders Danielsson and Thorsten Altenkirch. Mixing
-- Induction and Coinduction. Draft 2009.

module MapIterateSL where

open import Coinduction

open import Data.Stream

------------------------------------------------------------------------------

map-iterate : ∀ {A} (f : A → A) (x : A) →
              map f (iterate f x) ≈ iterate f (f x)
map-iterate f x = f x ∷ ♯ map-iterate f (f x)
