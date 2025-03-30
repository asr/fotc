
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Numeric.Natural ( Natural )
import Test.QuickCheck

-- From quickcheck-instances 0.3.32.
instance Arbitrary Natural where
  arbitrary = arbitrarySizedNatural
  shrink    = shrinkIntegral

type Nat = Natural

gcd' :: Nat -> Nat -> Nat
gcd' m n =
  if n == 0
  then m
  else if m == 0 then n else if m > n then gcd' (m - n) n else gcd' m (n - m)

prop :: Nat -> Nat -> Bool
prop m n = gcd' m n == gcd m n

main :: IO ()
main = quickCheck prop
