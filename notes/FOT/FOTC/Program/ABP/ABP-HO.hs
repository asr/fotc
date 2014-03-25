------------------------------------------------------------------------------
-- The alternating bit protocol using higher-order functions
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

-- Tested with random 1.0.1.1, QuickCheck 2.6 and streams 3.2.

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

type SendTy a     = Stream a → Stream (Err Bit) → Stream (a, Bit)
type AckTy a      = Stream (Err (a, Bit)) → Stream Bit
type OutTy a      = Stream (Err (a, Bit)) → Stream a
type CorruptTy1 a = Stream (a, Bit) → Stream (Err (a, Bit))
type CorruptTy2   = Stream Bit → Stream (Err Bit)

hasH ∷ SendTy a → AckTy a → OutTy a → CorruptTy1 a → CorruptTy2 → Stream a →
       Stream (a, Bit)
hasH f1 f2 f3 g1 g2 is = f1 is (hdsH f1 f2 f3 g1 g2 is)

hbsH ∷ SendTy a → AckTy a → OutTy a → CorruptTy1 a → CorruptTy2 → Stream a →
       Stream (Err (a, Bit))
hbsH f1 f2 f3 g1 g2 is = g1 (hasH f1 f2 f3 g1 g2 is)

hcsH ∷ SendTy a → AckTy a → OutTy a → CorruptTy1 a → CorruptTy2 → Stream a →
       Stream Bit
hcsH f1 f2 f3 g1 g2 is = f2 (hbsH f1 f2 f3 g1 g2 is)

hdsH ∷ SendTy a → AckTy a → OutTy a → CorruptTy1 a → CorruptTy2 → Stream a →
       Stream (Err Bit)
hdsH f1 f2 f3 g1 g2 is = g2 (hcsH f1 f2 f3 g1 g2 is)

transferH ∷ SendTy a → AckTy a → OutTy a → CorruptTy1 a → CorruptTy2 →
            Stream a →
            Stream a
transferH f1 f2 f3 g1 g2 is = f3 (hbsH f1 f2 f3 g1 g2 is)

-- The ABP transfer function.
abpTransH ∷ Bit → Stream Bit → Stream Bit → Stream a → Stream a
abpTransH b os1 os2 is =
  transferH (sendH b) (ackH b) (outH b) (corruptH os1) (corruptH os2) is

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
