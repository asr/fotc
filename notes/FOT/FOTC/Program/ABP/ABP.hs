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
await b input@(i :> is) (Ok b₀ :> ds) =
  if b == b₀ then send (not b) is ds else (i, b) :> await b input ds
await b input@(i :> _) (Error :> ds) = (i, b) :> await b input ds

-- The receiver functions.
ack ∷ Bit → Stream (Err (a, Bit)) → Stream Bit
ack b (Ok (_, b₀) :> bs) =
 if b == b₀ then b :> ack (not b) bs else not b :> ack b bs
ack b (Error :> bs) = not b :> ack b bs

out ∷ Bit → Stream (Err (a, Bit)) → Stream a
out b (Ok (i, b₀) :> bs) = if b == b₀ then i :> out (not b) bs else out b bs
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
trans b os₀ os₁ is = out b bs
  where
  as ∷ Stream (a, Bit)
  as = send b is ds

  bs ∷ Stream (Err (a, Bit))
  bs = corrupt os₀ as

  cs ∷ Stream Bit
  cs = ack b bs

  ds ∷ Stream (Err Bit)
  ds = corrupt os₁ cs

-- Simulation.
main ∷ IO ()
main = do
  gen₁ ← newStdGen
  gen₂ ← newStdGen

  let input ∷ Stream Int
      input = S.iterate (+ 1) 1

      channel₁ , channel₂ ∷ Stream Bool
      channel₁ = S.fromList $ randoms gen₁
      channel₂ = S.fromList $ randoms gen₂

      initialBit ∷ Bool
      initialBit = False

      output ∷ Stream Int
      output = trans initialBit channel₁ channel₂ input

  print gen₁
  print gen₂
  print (S.take 20 output)
