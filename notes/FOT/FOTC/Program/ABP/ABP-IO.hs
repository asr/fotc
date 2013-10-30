{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

------------------------------------------------------------------------------
module Main where

import Control.Monad ( when )

import Data.Stream.Infinite as S
  ( Stream( (:>) )
  , take
  )

-- import Test.QuickCheck
--   ( Arbitrary(arbitrary)
--   , quickCheck
--   )

------------------------------------------------------------------------------
type Bit = Bool

-- Data type used to model the fair unreliable transmission channel.
data Err a = Error | Ok a
             deriving Show

-- The mutual sender functions.
send ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
send b input@(i :> _) ds = (i , b) :> await b input ds

await ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
await b input@(i :> is) (Ok b0 :> ds) =
  if b == b0 then send (not b) is ds else (i, b) :> await b input ds
await b input@(i :> _) (Error :> ds) = (i, b) :> await b input ds

-- The receiver functions.
ack ∷ Bit → Stream (Err (a, Bit)) → Stream Bit
ack b (Ok (_, b0) :> bs) =
 if b == b0 then b :> ack (not b) bs else not b :> ack b bs
ack b (Error :> bs) = not b :> ack b bs

-- out ∷ Bit → Stream (Err (a, Bit)) → Stream a
-- out b (Ok (i, b0) :> bs) = if b == b0 then i :> out (not b) bs else out b bs
-- out b (Error :> bs)      = out b bs

out ∷ Integer → Bit → Stream (Err (Int, Bit)) → IO (Stream Int)
out n b (Ok (i, b0) :> bs) =
  if b == b0
  then do
    when (n <= 1) $
      putStrLn $ "out ok, b == b0, b:> "
                 ++ show b ++ " b0: " ++ show b0 ++ " i: " ++ show i
    xs ← out (n + 1) (not b) bs
    return $ i :> xs
  else do
    xs ← out (n + 1) b bs
    return xs
out n b (Error :> bs) = do
  when (n <= 1) $ print "out: Error"
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
abpTrans b os0 os1 is = out 0 b bs
  where
  as ∷ Stream (Int, Bit)
  as = send b is ds

  bs ∷ Stream (Err (Int, Bit))
  bs = corrupt os0 as

  cs ∷ Stream Bit
  cs = ack b bs

  ds ∷ Stream (Err Bit)
  ds = corrupt os1 cs

------------------------------------------------------------------------------
-- Testing

-- instance Arbitrary a ⇒ Arbitrary (Stream a) where
--   arbitrary = liftM2 (:>) arbitrary arbitrary

-- prop ∷ Stream Int → Stream Bit → Stream Bit → Bit → Bool
-- prop input os1 os2 initialBit =
--   S.take 10 input == S.take 10 (abpTrans initialBit os1 os2 input)

------------------------------------------------------------------------------
-- Simulation

os0' ∷ Stream Bit
os0' = True :> False :> os0'

os1' ∷ Stream Bit
os1' = False :> True :> os1'

is' ∷ Stream Int
is' = 1 :> 2 :> 3 :> is'

main ∷ IO ()
main = do
  xs ← abpTrans True os0' os1' is'
  print $ S.take 10 xs
