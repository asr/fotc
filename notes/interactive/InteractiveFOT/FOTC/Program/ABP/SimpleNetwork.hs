------------------------------------------------------------------------------
-- A simple network
------------------------------------------------------------------------------

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnicodeSyntax       #-}

-- From (Sander, 1992, pp. 68-69).

-- Tested with streams 3.2.1.

module SimpleNetwork where

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
trans' g1 g2 is = g2 (hys g1 g2 is)
hys    g1 g2 is = g1 (trans' g1 g2 is) is

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
