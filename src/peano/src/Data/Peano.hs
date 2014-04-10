-----------------------------------------------------------------------------
-- |
-- Module      : Data.Peano
-- Copyright   : (c) Andrés Sicard-Ramírez 2009-2014
-- License     : See the file LICENSE.
--
-- Maintainer  : Andrés Sicard-Ramírez <asr@eafit.edu.co>
-- Stability   : experimental
--
-- Peano numbers.
-----------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

module Data.Peano
  ( (∸)
  , Nat(Zero, Succ)
  )
where

import Control.Monad ( liftM )

import Test.QuickCheck
  ( Arbitrary(arbitrary)
  , oneof
  )

-----------------------------------------------------------------------------
-- From http://byorgey.wordpress.com/2010/11/:
-- Note that the auto-derived Ord instance have exactly the right
-- behavior due to the fact that we happened to list the Zero
-- constructor first.

-- | Peano natural numbers.
data Nat = Zero | Succ Nat
         deriving (Eq, Ord)

nat2Integer ∷ Nat → Integer
nat2Integer Zero     = 0
nat2Integer (Succ n) = 1 + nat2Integer n

nat2Int ∷ Nat → Int
nat2Int Zero     = 0
nat2Int (Succ n) = 1 + nat2Int n

-- Adapted from http://byorgey.wordpress.com/2010/11/.
instance Num Nat where
  Zero   + n = n
  Succ m + n = Succ (m + n)

  Zero   * _ = Zero
  Succ m * n = n + m * n

  m      - Zero   = m
  Zero   - Succ _ = Zero
  Succ m - Succ n = m - n

  abs    _ = error "abs"
  negate _ = error "negate"
  signum n = n

  fromInteger 0 = Zero
  fromInteger n = if n < 0
                  then error "fromInteger: negative value"
                  else Succ (fromInteger (n - 1))

-- | Truncated subtraction.
(∸) ∷ Nat → Nat → Nat
(∸) = (-)

instance Real Nat where
  toRational = toRational . nat2Integer

instance Enum Nat where
  fromEnum = fromEnum . nat2Int

  toEnum 0 = Zero
  toEnum n = if n > 0
             then Succ (toEnum (n - 1))
             else error "toEnum: negative value"

instance Integral Nat where
  quotRem m n = (f , s)
    where
    r ∷ (Int, Int)
    r = quotRem (nat2Int m) (nat2Int n)

    f ∷ Nat
    f = toEnum (fst r)

    s ∷ Nat
    s = toEnum (snd r)

  toInteger = nat2Integer

instance Show Nat where
  show = show . nat2Integer

-- QuickCheck instance. Adapted from the list instance in [Claessen
-- and Hughes, 2000].
instance Arbitrary Nat where
  arbitrary = oneof [return Zero, liftM Succ arbitrary]

------------------------------------------------------------------------------
-- References:

-- Claessen, Koen and Hughes, John (2000). QuickCheck: A Lightweight
-- Tool for Random Testing of Haskell programs. In: Proceedings of the
-- fifth ACM SIGPLAN International Conference on Functional Programming
-- (ICFP ’00), pp. 268–279.
