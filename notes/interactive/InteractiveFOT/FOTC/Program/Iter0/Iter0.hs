
module Iter0 where

import Data.Peano ( Nat(Z) )

iter0 :: (Nat -> Nat) -> Nat -> [Nat]
iter0 f n = if n == Z then [] else n : iter0 f (f n)
