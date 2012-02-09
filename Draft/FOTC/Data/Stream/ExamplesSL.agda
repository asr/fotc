------------------------------------------------------------------------------
-- Stream examples using the standard library
------------------------------------------------------------------------------

-- Tested with the development version of the standard library on
-- 02 February 2012.

module Draft.FOTC.Data.Stream.ExamplesSL where

open import Data.Nat
open import Data.Stream

open import Coinduction

------------------------------------------------------------------------------

zeros : Stream ℕ
zeros = zero ∷ ♯ zeros
