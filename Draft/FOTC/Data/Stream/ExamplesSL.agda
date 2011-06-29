------------------------------------------------------------------------------
-- Stream examples using the standard libray
------------------------------------------------------------------------------

-- Tested with the development version on 29 June 2011.

module Draft.FOTC.Data.Stream.ExamplesSL where

open import Data.Nat
open import Data.Stream

open import Coinduction

------------------------------------------------------------------------------

zeros : Stream ℕ
zeros = zero ∷ ♯ zeros
