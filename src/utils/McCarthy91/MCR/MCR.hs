{-# LANGUAGE UnicodeSyntax #-}

-- We test some properties of the relation MCR with QuickCheck.

-- Tested with QuickCheck 2.10.1

module Main ( main ) where

import Test.QuickCheck

-- Local imports
import Data.Peano ( PeanoNat(S) )

------------------------------------------------------------------------------
-- The MCR relation.
mcr ∷ PeanoNat → PeanoNat → Bool
mcr m n = (101 - m) < (101 - n)

-- Some properties of the relation MCR

prop1 ∷ PeanoNat → PeanoNat → Property
prop1 m n = mcr (S m) (S n) ==> mcr m n

prop2 ∷ PeanoNat → PeanoNat → Property
prop2 m n = mcr m n ==> mcr (S m) (S n)

prop3 ∷ PeanoNat → PeanoNat → Property
prop3 m n = m > 95 && n > 95 && mcr m n ==> mcr (S m) (S n)

prop4 ∷ PeanoNat → PeanoNat → Bool
prop4 m n = mcr m n == (n < m && n < 101)

main ∷ IO ()
main = do
  quickCheck prop1   -- Passed
  quickCheck prop2   -- Passed
  quickCheck prop3   -- Gave up
  quickCheckWith (stdArgs { maxDiscardRatio = 100 }) prop3  -- Gave up
  quickCheck prop4  -- Passed
