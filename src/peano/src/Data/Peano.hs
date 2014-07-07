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
  , int2Nat
  , Nat(Z, S)
  , nat2Int
  )
where

import Control.Monad ( liftM )

import Test.QuickCheck
  ( Arbitrary(arbitrary)
  , oneof
  )

-----------------------------------------------------------------------------
-- From http://byorgey.wordpress.com/2010/11/:
--
-- Note that the auto-derived Ord instance have exactly the right
-- behavior due to the fact that we happened to list the Z constructor
-- first.

-- | Peano natural numbers.
data Nat = Z | S Nat
         deriving (Eq, Ord)

nat2Integer ∷ Nat → Integer
nat2Integer Z     = 0
nat2Integer (S n) = 1 + nat2Integer n

nat2Int ∷ Nat → Int
nat2Int Z     = 0
nat2Int (S n) = 1 + nat2Int n

int2Nat ∷ Int → Nat
int2Nat n | n < 0 = error "int2Nat: negative argument"
int2Nat 0         = Z
int2Nat n         = S $ int2Nat (n - 1)

-- Adapted from http://byorgey.wordpress.com/2010/11/.
instance Num Nat where
  Z   + n = n
  S m + n = S (m + n)

  Z   * _ = Z
  S m * n = n + m * n

  m   - Z   = m
  Z   - S _ = Z
  S m - S n = m - n

  abs n = n

  negate _ = error "negate"

  signum Z     = 0
  signum (S _) = 1

  fromInteger 0 = Z
  fromInteger n = if n < 0
                  then error "fromInteger: negative value"
                  else S (fromInteger (n - 1))

-- | Truncated subtraction.
(∸) ∷ Nat → Nat → Nat
(∸) = (-)

instance Real Nat where
  toRational = toRational . nat2Integer

instance Enum Nat where
  fromEnum = fromEnum . nat2Int

  toEnum 0 = Z
  toEnum n = if n > 0
             then S (toEnum (n - 1))
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
  arbitrary = oneof [return Z, liftM S arbitrary]

------------------------------------------------------------------------------
-- References:

-- Claessen, Koen and Hughes, John (2000). QuickCheck: A Lightweight
-- Tool for Random Testing of Haskell programs. In: Proceedings of the
-- fifth ACM SIGPLAN International Conference on Functional Programming
-- (ICFP ’00), pp. 268–279.
