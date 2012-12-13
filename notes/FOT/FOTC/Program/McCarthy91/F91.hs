{-# LANGUAGE UnicodeSyntax #-}

import Data.Peano

f₉₁ ∷ Nat → Nat
f₉₁ n = if n > 100 then n - 10 else f₉₁ (f₉₁ (n + 11))
