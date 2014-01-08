------------------------------------------------------------------------------
-- Stream properties using the standard library
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Stream.PropertiesSL where

open import Data.Nat
open import Data.Stream
open import Coinduction
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

zeros : Stream ℕ
zeros = 0 ∷ ♯ zeros

-- TODO (07 November 2013): Why the identity type works with infinite
-- lists?
zeros≡zeros : zeros ≡ zeros
zeros≡zeros = refl
