-- The thesis version.

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main where

import Data.Stream.Infinite ( Stream( (:>) ) )

type Bit = Bool

-- Data type used to model possible corrupted messages.
data Err a = Error | Ok a

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
abpTransH b os1 os2 is = outH b bs
  where
  as ∷ Stream (a, Bit)
  as = sendH b is ds

  bs ∷ Stream (Err (a, Bit))
  bs = corruptH os1 as

  cs ∷ Stream Bit
  cs = ackH b bs

  ds ∷ Stream (Err Bit)
  ds = corruptH os2 cs
