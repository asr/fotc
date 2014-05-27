{-# LANGUAGE UnicodeSyntax #-}

import Data.Peano

iter0 ∷ (Nat → Nat) → Nat → [Nat]
iter0 f n = if n == Z then [] else n : iter0 f (f n)
