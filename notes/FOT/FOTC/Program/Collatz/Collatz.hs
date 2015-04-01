{-# LANGUAGE CPP           #-}
{-# LANGUAGE UnicodeSyntax #-}

module Collatz where

#if __GLASGOW_HASKELL__ >= 710
import Numeric.Natural
#else
import Data.Peano
#endif

#if __GLASGOW_HASKELL__ >= 710
type Nat = Natural
#endif

collatz ∷ Nat → Nat
collatz 0 = 1
collatz 1 = 1
collatz n = if even n then collatz (div n 2) else collatz (3 * n + 1)
