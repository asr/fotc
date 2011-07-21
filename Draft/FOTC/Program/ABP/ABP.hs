{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

-- Tested with GHC 7.0.4.

-- The alternating bit protocol following [1].

-- [1]. Peter Dybjer and Herbert Sander. A functional programming
-- approach to the specification and verification of concurrent
-- systems. Formal Aspects of Computing, 1:303-319, 1989.

------------------------------------------------------------------------------

type Stream a = [a]

type Bit = Bool

-- Data type used to model the fair unreliable tranmission channel.
data Err a  = Error | Ok a
            deriving Show

-- The sender functions.
send ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
send _ []            _  = error "Impossible (send)"
send b input@(i : _) ds = (i , b) : await b input ds

await ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
await _ _              []           = error "Impossible (await eq. 1)"
await _ []             _            = error "Impossible (await eq. 2)"
await b input@(i : is) (Ok b0 : ds) =
  if b == b0 then send (not b) is ds else (i, b) : await b input ds
await b input@(i : _) (Error : ds) = (i, b) : await b input ds

-- The receiver functions.
ack ∷ Bit → Stream (Err (a, Bit)) → Stream Bit
ack _ []                = error "Impossible (ack)"
ack b (Ok (_, b0) : bs) =
  if b == b0 then b : ack (not b) bs else not b : ack b bs
ack b (Error : bs) = not b : ack b bs

out ∷ Bit → Stream (Err (a, Bit)) → Stream a
out _ []                = error "Impossible (out)"
out b (Ok (i, b0) : bs) = if b == b0 then i : out (not b) bs else out b bs
out b (Error : bs)      = out b bs

-- Model the fair unreliable tranmission channel.
corrupt ∷ Stream Bit → Stream a → Stream (Err a)
corrupt (False : os) (_ : xs) = Error : corrupt os xs
corrupt (True : os)  (x : xs) = Ok x  : corrupt os xs
corrupt _            _        = error "Impossible (corrupt)"

-- The ABP transfer function.
-- (Requires the flag ScopedTypeVariables to write the type signatures
-- of the functions defined in the where clauses).
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

  let input ∷ Stream Int
      input = [1 ..]

      -- TODO: The channels should be ramdon.
      channel ∷ [Bool]
      channel = concat $ repeat [True,False,False,False]

      initialBit ∷ Bool
      initialBit = False

      output ∷ Stream Int
      output = trans initialBit channel channel input

  print (take 10 output)
