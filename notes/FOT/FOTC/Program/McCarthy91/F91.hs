{-# LANGUAGE UnicodeSyntax #-}

import Data.Peano

f₉₁ ∷ Nat → Nat
f₉₁ n | n > 100   = n - 10
      | otherwise = f₉₁ (f₉₁ (n + 11))
