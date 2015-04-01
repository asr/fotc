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
  , int2nat
  , Nat(Z, S)
  , nat2int
  )
where

import Test.QuickCheck
  ( Arbitrary(arbitrary)
    , arbitrarySizedNatural
  )

-----------------------------------------------------------------------------
-- Auxiliary functions

mapTuple ∷ (a → b) → (a, a) → (b, b)
mapTuple f (a1, a2) = (f a1, f a2)

-----------------------------------------------------------------------------
-- From http://byorgey.wordpress.com/2010/11/:
--
-- Note that the auto-derived Ord instance have exactly the right
-- behavior due to the fact that we happened to list the Z constructor
-- first.

-- | Peano natural numbers.
data Nat = Z | S Nat
         deriving (Eq, Ord)

nat2integer ∷ Nat → Integer
nat2integer Z     = 0
nat2integer (S n) = 1 + nat2integer n

nat2int ∷ Nat → Int
nat2int Z     = 0
nat2int (S n) = 1 + nat2int n

int2nat ∷ Int → Nat
int2nat n | n < 0 = error "int2Nat: negative argument"
int2nat 0         = Z
int2nat n         = S $ int2nat (n - 1)

integer2nat ∷ Integer → Nat
integer2nat n | n < 0 = error "integer2Nat: negative argument"
integer2nat 0         = Z
integer2nat n         = S $ integer2nat (n - 1)

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

  -- In the @Integral@ class, @div@ is defined via @divMod@ which uses
  -- @negate@. See
  -- https://downloads.haskell.org/~ghc/7.8.4/docs/html/libraries/base-4.7.0.2/src/GHC-Real.html#div
  negate n = n

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
  toRational = toRational . nat2integer

instance Enum Nat where
  fromEnum = fromEnum . nat2int

  toEnum 0 = Z
  toEnum n = if n > 0
             then S (toEnum (n - 1))
             else error "toEnum: negative value"

instance Integral Nat where
  quotRem m n = mapTuple integer2nat $ quotRem (nat2integer m) (nat2integer n)

  -- TODO (07 July 2014). Why is this definition necessary?
  divMod m n = mapTuple integer2nat $ divMod (nat2integer m) (nat2integer n)

  toInteger = nat2integer

instance Show Nat where
  show = show . nat2integer

instance Arbitrary Nat where
  arbitrary = arbitrarySizedNatural
