{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

------------------------------------------------------------------------------
module Main where

import Control.Monad ( when, replicateM )

import Data.Stream.Infinite as S
  ( Stream((:>))
  , fromList
  , take
  )

-- import Test.QuickCheck
--   ( Arbitrary(arbitrary)
--   , quickCheck
--   )

import System.Random ( newStdGen, random, randoms )

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

-- outH ∷ Bit → Stream (Err (a, Bit)) → Stream a
-- outH b (Ok (i, b') :> bs) = if b == b' then i :> outH (not b) bs else outH b bs
-- outH b (Error :> bs)      = outH b bs

outH ∷ Integer → Bit → Stream (Err (Int, Bit)) → IO (Stream Int)
outH n b (Ok (i, b') :> bs) =
  if b == b'
  then do
    when (n <= 4) $
      putStrLn $ "outH (Ok b == b'): "
                 ++ "b: " ++ show b ++ " b': " ++ show b' ++ " i: " ++ show i

    xs ← outH (n + 1) (not b) bs
    return $ i :> xs
  else do
    when (n <= 4) $
      putStrLn $ "outH (Ok b ≠ b'): "
                 ++ "b: " ++ show b ++ " b': " ++ show b' ++ " i: " ++ show i

    xs ← outH (n + 1) b bs
    return xs
outH n b (Error :> bs) = do
  when (n <= 4) $ putStrLn "outH (Error)"
  xs ← outH (n + 1) b bs
  return xs

-- The fair unreliable transmission channel.
corruptH ∷ Stream Bit → Stream a → Stream (Err a)
corruptH (False :> os) (_ :> xs) = Error :> corruptH os xs
corruptH (True :> os)  (x :> xs) = Ok x  :> corruptH os xs

-- The ABP transfer function.
--
-- Requires the ScopedTypeVariables flag to write the type signatures
-- of the terms defined in the where clauses.
--
-- N.B. We use @forall@ instead of @∀@ because it generates an error
-- with HLint (the issue is from haskell-src-exts).
abpTransH ∷ Bit → Stream Bit → Stream Bit → Stream Int → IO (Stream Int)
abpTransH b os1 os2 is = outH 0 b bs
  where
  as ∷ Stream (Int, Bit)
  as = sendH b is ds

  bs ∷ Stream (Err (Int, Bit))
  bs = corruptH os1 as

  cs ∷ Stream Bit
  cs = ackH b bs

  ds ∷ Stream (Err Bit)
  ds = corruptH os2 cs

------------------------------------------------------------------------------
-- Testing

-- instance Arbitrary a ⇒ Arbitrary (Stream a) where
--   arbitrary = liftM2 (:>) arbitrary arbitrary

-- prop ∷ Stream Int → Stream Bit → Stream Bit → Bit → Bool
-- prop input os2 os2 initialBit =
--   S.take 10 input == S.take 10 (abpTrans initialBit os2 os2 input)

------------------------------------------------------------------------------
-- Simulation

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

      n ∷ Int
      n = 100

  js ← abpTransH startBit os1 os2 is

  print $ S.take n js
  print $ S.take n is == S.take n js
