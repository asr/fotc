{-# LANGUAGE CPP           #-}
{-# LANGUAGE UnicodeSyntax #-}

#if __GLASGOW_HASKELL__ >= 710
import Numeric.Natural
#else
import Data.Peano
#endif

import Test.QuickCheck

#if __GLASGOW_HASKELL__ >= 710
type Nat = Natural
#endif

gcd' ∷ Nat → Nat → Nat
gcd' m n =
  if n == 0
  then m
  else if m == 0 then n else if m > n then gcd' (m - n) n else gcd' m (n - m)

prop ∷ Nat → Nat → Bool
prop m n = gcd' m n == gcd m n

main ∷ IO ()
main = quickCheck prop
