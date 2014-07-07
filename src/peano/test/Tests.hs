{-# LANGUAGE UnicodeSyntax #-}

module Tests where

import Data.Peano                        ( Nat )
import Distribution.TestSuite.QuickCheck ( Test, testProperty )
import Test.QuickCheck                   ( (==>), Property )

-- From:
-- http://www.haskell.org/ghc/docs/7.8.2/html/libraries/base-4.7.0.0/Prelude.html#t:Num
prop_signum ∷ Nat → Bool
prop_signum x = abs x * signum x == x

-- In non-negative integers @div@ and @quot@ should be have the same
-- behaviour.
prop_div_quot ∷ Nat → Nat → Property
prop_div_quot n d = n >= 0 && d > 0 ==> n `div` d == n `quot` d

tests ∷ IO [Test]
tests = return [ testProperty "signum" prop_signum
               , testProperty "div_quot" prop_div_quot
               ]
