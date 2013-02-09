{-# LANGUAGE UnicodeSyntax #-}

import Data.Peano

gcd' ∷ Nat → Nat → Nat
gcd' m n =
  if n == 0
  then m
  else if m == 0 then n else if m > n then gcd' (m - n) n else gcd' m (n - m)
