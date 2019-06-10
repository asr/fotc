{-# LANGUAGE UnicodeSyntax #-}

module Iter0 where

import Data.Peano ( PeanoNat(Z) )

iter0 ∷ (PeanoNat → PeanoNat) → PeanoNat → [PeanoNat]
iter0 f n = if n == Z then [] else n : iter0 f (f n)
