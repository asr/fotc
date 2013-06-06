{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

-- The alternating bit protocol following (Dybjer and Herbert 1989).

-- References:
--
-- • Peter Dybjer and Herbert Sander. A functional programming
--   approach to the specification and verification of concurrent
--   systems. Formal Aspects of Computing, 1:303-319, 1989.

-- Tested with the streams library v. 3.1.
------------------------------------------------------------------------------

module ABP where

import Data.Stream.Infinite as S ( fromList, iterate, Stream((:>)), take )

import System.Random ( newStdGen, randoms )

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

out ∷ Bit → Stream (Err (a, Bit)) → Stream a
out b (Ok (i, b0) :> bs) = if b == b0 then i :> out (not b) bs else out b bs
out b (Error :> bs)      = out b bs

-- The fair unreliable transmission channel.
corrupt ∷ Stream Bit → Stream a → Stream (Err a)
corrupt (False :> os) (_ :> xs) = Error :> corrupt os xs
corrupt (True :> os)  (x :> xs) = Ok x  :> corrupt os xs

-- The ABP transfer function.
--
-- Requires the flag ScopedTypeVariables to write the type signatures
-- of the terms defined in the where clauses.
trans ∷ forall a. Bit → Stream Bit → Stream Bit → Stream a → Stream a
trans b os0 os1 is = out b bs
  where
  as ∷ Stream (a, Bit)
  as = send b is ds

  bs ∷ Stream (Err (a, Bit))
  bs = corrupt os0 as

  cs ∷ Stream Bit
  cs = ack b bs

  ds ∷ Stream (Err Bit)
  ds = corrupt os1 cs

-- Simulation.
main ∷ IO ()
main = do
  gen1 ← newStdGen
  gen2 ← newStdGen

  let input ∷ Stream Int
      input = S.iterate (+ 1) 1

      channel1 , channel2 ∷ Stream Bool
      channel1 = S.fromList $ randoms gen1
      channel2 = S.fromList $ randoms gen2

      initialBit ∷ Bool
      initialBit = False

      output ∷ Stream Int
      output = trans initialBit channel1 channel2 input

  print gen1
  print gen2
  print (S.take 20 output)
