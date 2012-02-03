-- Tested with GHC 7.2.2.

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax #-}

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
abpsend ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
abpsend _ []            _  = error "Impossible (abpsend)"
abpsend b input@(i : _) ds = (i , b) : await b input ds

await ∷ Bit → Stream a → Stream (Err Bit) → Stream (a, Bit)
await _ _              []           = error "Impossible (await eq. 1)"
await _ []             _            = error "Impossible (await eq. 2)"
await b input@(i : is) (Ok b0 : ds) =
  if b == b0 then abpsend (not b) is ds else (i, b) : await b input ds
await b input@(i : _) (Error : ds) = (i, b) : await b input ds

-- The receiver functions.
abpack ∷ Bit → Stream (Err (a, Bit)) → Stream Bit
abpack _ []                = error "Impossible (ack)"
abpack b (Ok (_, b0) : bs) =
  if b == b0 then b : abpack (not b) bs else not b : abpack b bs
abpack b (Error : bs) = not b : abpack b bs

abpout ∷ Bit → Stream (Err (a, Bit)) → Stream a
abpout _ []                = error "Impossible (abpout)"
abpout b (Ok (i, b0) : bs) =
  if b == b0 then i : abpout (not b) bs else abpout b bs
abpout b (Error : bs)      = abpout b bs

-- Model the fair unreliable tranmission channel.
corrupt ∷ Stream Bit → Stream a → Stream (Err a)
corrupt (False : os) (_ : xs) = Error : corrupt os xs
corrupt (True : os)  (x : xs) = Ok x  : corrupt os xs
corrupt _            _        = error "Impossible (corrupt)"

-- The ABP transfer function.
--
-- (Requires the flag ScopedTypeVariables to write the type signatures
-- of the terms defined in the where clauses).
abptrans ∷ forall a. Bit → Stream Bit → Stream Bit → Stream a → Stream a
abptrans b os0 os1 is = abpout b bs
  where
    as ∷ Stream (a, Bit)
    as = abpsend b is ds

    bs ∷ Stream (Err (a, Bit))
    bs = corrupt os0 as

    cs ∷ Stream Bit
    cs = abpack b bs

    ds ∷ Stream (Err Bit)
    ds = corrupt os1 cs

-- Simulation.

main ∷ IO ()
main = do

  let input ∷ Stream Int
      input = [1 ..]

      -- TODO: The channels should be random.
      channel ∷ [Bool]
      channel = concat $ repeat [True,False,False,False]

      initialBit ∷ Bool
      initialBit = False

      output ∷ Stream Int
      output = abptrans initialBit channel channel input

  print (take 10 output)
