{-# LANGUAGE UnicodeSyntax #-}

module F91 where

import Data.Peano

f91 ∷ Nat → Nat
f91 n = if n > 100 then n - 10 else f91 (f91 (n + 11))
