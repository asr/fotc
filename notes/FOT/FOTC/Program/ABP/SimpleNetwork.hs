------------------------------------------------------------------------------
-- A simple network
------------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
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

trans ∷ forall a. Stream a → Stream a
trans is = os
  where
  ys ∷ Stream a
  ys = f1 os is
  os = f2 ys

type Ty a = (Stream a → Stream a → Stream a) → (Stream a → Stream a) →
            Stream a → Stream a

trans', hys ∷ Ty a
trans' f1 f2 is = f2 (hys f1 f2 is)
hys    f1 f2 is = f1 (trans' f1 f2 is) is
