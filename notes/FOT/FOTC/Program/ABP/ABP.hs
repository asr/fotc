{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

-- The alternating bit protocol following Dybjer and Herbert (1989).

-- References:
--
-- • Dybjer, Peter and Herbert P. Sander (1989). A Functional
--   Programming Approach to the Speciﬁcation and Veriﬁcation of
--   Concurrent Systems. In: Formal Aspects of Computing 1,
--   pp. 303–319.

-- Tested with random 1.0.1.1, QuickCheck 2.6 and streams 3.1.1.

------------------------------------------------------------------------------
module Main where

import Control.Monad ( liftM2, replicateM )

import Data.Stream.Infinite as S
  ( Stream( (:>) )
  , fromList
  , take
  )

import System.Random ( newStdGen, random, randoms )

import Test.QuickCheck
  ( Arbitrary( arbitrary ), quickCheck )

------------------------------------------------------------------------------
type Bit = Bool

-- Data type used to model the fair unreliable transmission channel.
data Err a = Error | Ok a
             deriving Show

-- The mutual sender functions.
send ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
send b input@(i :> _) ds = (i , b) :> await b input ds

await ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
await b input@(i :> is) (Ok b' :> ds) =
  if b == b' then send (not b) is ds else (i, b) :> await b input ds
await b input@(i :> _) (Error :> ds) = error "await" -- (i, b) :> await b input ds

-- The receiver functions.
ack ∷ Bit → Stream (Err (a, Bit)) → Stream Bit
ack b (Ok (_, b') :> bs) =
 if b == b' then b :> ack (not b) bs else not b :> ack b bs
ack b (Error :> bs) = not b :> ack b bs

out ∷ Bit → Stream (Err (a, Bit)) → Stream a
out b (Ok (i, b') :> bs) = if b == b' then i :> out (not b) bs else out b bs
out b (Error :> bs)      = out b bs

-- The fair unreliable transmission channel.
corrupt ∷ Stream Bit → Stream a → Stream (Err a)
corrupt (False :> os) (_ :> xs) = Error :> corrupt os xs
corrupt (True :> os)  (x :> xs) = Ok x  :> corrupt os xs

-- The ABP transfer function.
--
-- Requires the ScopedTypeVariables flag to write the type signatures
-- of the terms defined in the where clauses.
--
-- N.B. We use @forall@ instead of @∀@ because it generates an error
-- with HLint (the issue is from haskell-src-exts).
abpTrans ∷ forall a. Bit → Stream Bit → Stream Bit → Stream a → Stream a
abpTrans b os1 os2 is = out b bs
  where
  as ∷ Stream (a, Bit)
  as = send b is ds

  bs ∷ Stream (Err (a, Bit))
  bs = corrupt os1 as

  cs ∷ Stream Bit
  cs = ack b bs

  ds ∷ Stream (Err Bit)
  ds = corrupt os2 cs

------------------------------------------------------------------------------
-- Testing

instance Arbitrary a ⇒ Arbitrary (Stream a) where
  arbitrary = liftM2 (:>) arbitrary arbitrary

prop ∷ Stream Int → Stream Bit → Stream Bit → Bit → Bool
prop is os1 os2 startBit =
  S.take 10 is == S.take 10 (abpTrans startBit os1 os2 is)

-- main ∷ IO ()
-- main = quickCheck prop

------------------------------------------------------------------------------
-- Simulation

main ∷ IO ()
main = do

  [g1, g2, g3, g4] ← replicateM 4 newStdGen

  let is ∷ Stream Int
      is = S.fromList $ randoms g1

      os1, os2 ∷ Stream Bit
      os1 = S.fromList $ randoms g2
      os2 = True :> os2 -- S.fromList $ randoms g3

      startBit ∷ Bit
      startBit = fst $ random g4

      js ∷ Stream Int
      js = abpTrans startBit os1 os2 is

      n ∷ Int
      n = 1000

  print $ S.take n js
  print $ S.take n is == S.take n js
