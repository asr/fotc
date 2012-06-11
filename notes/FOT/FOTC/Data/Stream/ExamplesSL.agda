------------------------------------------------------------------------------
-- Stream examples using the standard library
------------------------------------------------------------------------------

-- Tested with the development version of the standard library on
-- 11 June 2012.

module ExamplesSL where

open import Data.Nat
open import Data.Stream

open import Coinduction

------------------------------------------------------------------------------

zeros : Stream ℕ
zeros = zero ∷ ♯ zeros
