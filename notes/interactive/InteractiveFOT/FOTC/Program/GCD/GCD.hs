
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Numeric.Natural ( Natural )
import Test.QuickCheck

-- From quickcheck-instances 0.3.32.
instance Arbitrary Natural where
  arbitrary = arbitrarySizedNatural
  shrink    = shrinkIntegral

type Nat = Natural

gcd1 :: Nat -> Nat -> Nat
gcd1 m n =
  if n == 0
  then m
  else if m == 0 then n else if m > n then gcd1 (m - n) n else gcd1 m (n - m)

gcd2 :: Nat -> Nat -> Nat
gcd2 0 n = n
gcd2 m 0 = m
gcd2 m n = if m > n then gcd2 (m - n) n else gcd2 m (n - m)


prop1 :: Nat -> Nat -> Bool
prop1 m n = gcd1 m n == gcd m n

prop2 :: Nat -> Nat -> Bool
prop2 m n = gcd2 m n == gcd m n

main :: IO ()
main = do
  quickCheck prop1
  quickCheck prop2
