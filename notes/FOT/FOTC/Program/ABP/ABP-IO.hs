{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

------------------------------------------------------------------------------
module Main where

import Control.Monad ( when, replicateM )

import Data.Stream.Infinite as S
  ( Stream( (:>) )
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

-- Data type used to model the fair unreliable transmission channel.
data Err a = Error | Ok a
             deriving Show

-- The mutual sender functions.
send ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
send b input@(i :> _) ds = (i , b) :> await b input ds

await ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
await b input@(i :> is) (Ok b' :> ds) =
  if b == b' then send (not b) is ds else (i, b) :> await b input ds
await b input@(i :> _) (Error :> ds) = (i, b) :> await b input ds

-- The receiver functions.
ack ∷ Bit → Stream (Err (a, Bit)) → Stream Bit
ack b (Ok (_, b') :> bs) =
 if b == b' then b :> ack (not b) bs else not b :> ack b bs
ack b (Error :> bs) = not b :> ack b bs

-- out ∷ Bit → Stream (Err (a, Bit)) → Stream a
-- out b (Ok (i, b') :> bs) = if b == b' then i :> out (not b) bs else out b bs
-- out b (Error :> bs)      = out b bs

out ∷ Integer → Bit → Stream (Err (Int, Bit)) → IO (Stream Int)
out n b (Ok (i, b') :> bs) =
  if b == b'
  then do
    when (n <= 4) $
      putStrLn $ "out (Ok b == b'): "
                 ++ "b: " ++ show b ++ " b': " ++ show b' ++ " i: " ++ show i

    xs ← out (n + 1) (not b) bs
    return $ i :> xs
  else do
    when (n <= 4) $
      putStrLn $ "out (Ok b ≠ b'): "
                 ++ "b: " ++ show b ++ " b': " ++ show b' ++ " i: " ++ show i

    xs ← out (n + 1) b bs
    return xs
out n b (Error :> bs) = do
  when (n <= 4) $ putStrLn "out (Error)"
  xs ← out (n + 1) b bs
  return xs

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
abpTrans ∷ Bit → Stream Bit → Stream Bit → Stream Int → IO (Stream Int)
abpTrans b os1 os2 is = out 0 b bs
  where
  as ∷ Stream (Int, Bit)
  as = send b is ds

  bs ∷ Stream (Err (Int, Bit))
  bs = corrupt os1 as

  cs ∷ Stream Bit
  cs = ack b bs

  ds ∷ Stream (Err Bit)
  ds = corrupt os2 cs

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

  js ← abpTrans startBit os1 os2 is

  print $ S.take n js
  print $ S.take n is == S.take n js
