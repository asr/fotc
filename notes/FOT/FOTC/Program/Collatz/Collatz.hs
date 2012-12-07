{-# LANGUAGE UnicodeSyntax #-}

import Data.Peano

collatz ∷ Nat → Nat
collatz 0 = 1
collatz 1 = 1
collatz n = if even n then collatz (div n 2) else collatz (3 * n + 1)
