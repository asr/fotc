{-# LANGUAGE UnicodeSyntax #-}

import Data.Peano

iter₀ ∷ (Nat → Nat) → Nat → [Nat]
iter₀ f n = if n == Zero then [] else n : iter₀ f (f n)
