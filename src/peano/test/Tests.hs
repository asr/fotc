{-# LANGUAGE UnicodeSyntax #-}

module Tests where

import Data.Peano                        ( Nat )
import Distribution.TestSuite.QuickCheck ( Test, testProperty )

-- From:
-- http://www.haskell.org/ghc/docs/7.8.2/html/libraries/base-4.7.0.0/Prelude.html#t:Num
prop_signum ∷ Nat → Bool
prop_signum x = abs x * signum x == x

tests ∷ IO [Test]
tests = return [ testProperty "signum" prop_signum ]
