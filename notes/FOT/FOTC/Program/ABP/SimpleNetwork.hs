------------------------------------------------------------------------------
-- A simple network
------------------------------------------------------------------------------

{-# LANGUAGE UnicodeSyntax #-}

-- From (Sander, 1992, pp. 68-69).
--
-- References:
--
-- • Sander, Herbert P. (1992). A Logic of Functional Programs with an
--   Application to Concurrency. PhD thesis. Department of Computer
--   Sciences: Chalmers University of Technology and University of
--   Gothenburg.

module Main where

import Data.Stream.Infinite ( Stream )

------------------------------------------------------------------------------

f1 ∷ Stream a → Stream a → Stream a
f1 = undefined

f2 ∷ Stream a → Stream a
f2 = undefined

is ∷ Stream a
is = undefined

ys ∷ Stream a
ys = f1 out is

out ∷ Stream a
out = f2 ys

type Ty a = (Stream a → Stream a → Stream a) → (Stream a → Stream a) →
            Stream a → Stream a

trans, hys ∷ Ty a
hys   f1 f2 is = f2 (hys f1 f2 is)
trans f1 f2 is = f1 (trans f1 f2 is) is
