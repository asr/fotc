-- Tested with GHC 7.6.1 and QuickCheck 2.5.1.1

{-# LANGUAGE UnicodeSyntax #-}

-- We test some properties of the relation MCR with QuickCheck.

module Main ( main ) where

import Data.Peano
import Test.QuickCheck

------------------------------------------------------------------------------
-- The MCR relation.
mcr ∷ Nat → Nat → Bool
mcr m n = (101 ∸ m) < (101 ∸ n)

-- Some properties of the relation MCR

prop1 ∷ Nat → Nat → Property
prop1 m n = mcr (Succ m) (Succ n) ==> mcr m n

prop2 ∷ Nat → Nat → Property
prop2 m n = mcr m n ==> mcr (Succ m) (Succ n)

prop3 ∷ Nat → Nat → Property
prop3 m n = m > 95 && n > 95 && mcr m n ==> mcr (Succ m) (Succ n)

prop4 ∷ Nat → Nat → Bool
prop4 m n = mcr m n == (n < m && n < 101)

main ∷ IO ()
main = do
  quickCheck prop1   -- Passed
  quickCheck prop2   -- Passed
  quickCheck prop3   -- Gave up
  quickCheckWith (stdArgs { maxDiscardRatio = 100 }) prop3  -- Failed
  quickCheck prop4  -- Passed
