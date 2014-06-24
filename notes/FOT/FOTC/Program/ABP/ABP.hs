{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax       #-}

-- The alternating bit protocol following Dybjer and Herbert (1989).

-- Tested with QuickCheck 2.7.5, random 1.0.1.1 and streams 3.2.

------------------------------------------------------------------------------
module Main where

import Control.Monad ( liftM2, replicateM )

import Data.Stream.Infinite ( Stream((:>)) )
import qualified Data.Stream.Infinite as S

import System.Random ( newStdGen, random, randoms )

import Test.QuickCheck
  ( Arbitrary(arbitrary), quickCheck )

------------------------------------------------------------------------------
type Bit = Bool

-- Data type used to model possible corrupted messages.
data Err a = Error | Ok a
             deriving Show

-- The mutual sender functions.
sendH ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
sendH b input@(i :> _) ds = (i , b) :> awaitH b input ds

awaitH ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
awaitH b input@(i :> is) (Ok b' :> ds) =
  if b == b' then sendH (not b) is ds else (i, b) :> awaitH b input ds
awaitH b input@(i :> _) (Error :> ds) = (i, b) :> awaitH b input ds

-- The receiver functions.
ackH ∷ Bit → Stream (Err (a, Bit)) → Stream Bit
ackH b (Ok (_, b') :> bs) =
 if b == b' then b :> ackH (not b) bs else not b :> ackH b bs
ackH b (Error :> bs) = not b :> ackH b bs

outH ∷ Bit → Stream (Err (a, Bit)) → Stream a
outH b (Ok (i, b') :> bs) = if b == b' then i :> outH (not b) bs else outH b bs
outH b (Error :> bs)      = outH b bs

-- The fair unreliable transmission channel.
corruptH ∷ Stream Bit → Stream a → Stream (Err a)
corruptH (False :> os) (_ :> xs) = Error :> corruptH os xs
corruptH (True :> os)  (x :> xs) = Ok x  :> corruptH os xs

-- The ABP transfer function.
--
-- Requires the ScopedTypeVariables flag to write the type signatures
-- of the terms defined in the where clauses.
--
-- N.B. @∀@ generates an error with HLint. The issue is from
-- haskell-src-exts 1.14.0. See
-- https://github.com/haskell-suite/haskell-src-exts/pull/59.
abpTransH ∷ ∀ a. Bit → Stream Bit → Stream Bit → Stream a → Stream a
abpTransH b os1 os2 is = js
  where
  as ∷ Stream (a, Bit)
  as = sendH b is ds

  bs ∷ Stream (Err (a, Bit))
  bs = corruptH os1 as

  cs ∷ Stream Bit
  cs = ackH b bs

  ds ∷ Stream (Err Bit)
  ds = corruptH os2 cs

  js ∷ Stream a
  js = outH b bs

------------------------------------------------------------------------------
-- Testing

instance Arbitrary a ⇒ Arbitrary (Stream a) where
  arbitrary = liftM2 (:>) arbitrary arbitrary

prop ∷ Bit → Stream Bit → Stream Bit → Stream Int → Bool
prop b os1 os2 is = S.take 10 is == S.take 10 (abpTransH b os1 os2 is)

-- main ∷ IO ()
-- main = quickCheck prop

------------------------------------------------------------------------------
-- Simulation
--
-- When the initial bit is False and the oracle stream os2 has only
-- Falses the ABP can transmit the first symbol (but it cannot
-- transmit the second one).
-- main ∷ IO ()
-- main = do

--   [g1, g2] ← replicateM 2 newStdGen

--   let is ∷ Stream Int
--       is = S.fromList $ randoms g1

--       os1, os2 ∷ Stream Bit
--       os1 = S.fromList $ randoms g2
--       os2 = S.repeat False

--       startBit ∷ Bit
--       startBit = False

--       js ∷ Stream Int
--       js = abpTransH startBit os1 os2 is

--       n ∷ Int
--       n = 1

--   print $ S.take n js
--   print $ S.take n is == S.take n js

------------------------------------------------------------------------------
-- General simulation

main ∷ IO ()
main = do

  [g1, g2, g3, g4] ← replicateM 4 newStdGen

  let is ∷ Stream Int
      is = S.fromList $ randoms g1

      os1, os2 ∷ Stream Bit
      os1 = S.fromList $ randoms g2
      os2 = S.fromList $ randoms g3

      startBit ∷ Bit
      startBit = fst $ random g4

      js ∷ Stream Int
      js = abpTransH startBit os1 os2 is

      n ∷ Int
      n = 1000

  print $ S.take n js
  print $ S.take n is == S.take n js

------------------------------------------------------------------------------
-- References
--
-- Dybjer, Peter and Herbert P. Sander (1989). A Functional
-- Programming Approach to the Specification and Verification of
-- Concurrent Systems. Formal Aspects of Computing 1, pp. 303–319.
