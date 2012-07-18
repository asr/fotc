------------------------------------------------------------------------------
-- Stream examples using the standard library
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Examples.FOTC.Data.Stream.ExamplesSL where

open import Data.Nat
open import Data.Stream

open import Coinduction

------------------------------------------------------------------------------

zeros : Stream ℕ
zeros = zero ∷ ♯ zeros
