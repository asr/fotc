{-# LANGUAGE UnicodeSyntax #-}

import Data.Peano
import Prelude hiding ( filter, tail )

------------------------------------------------------------------------------

data Stream a = Cons a (Stream a)

tail ∷ Stream a → Stream a
tail (Cons _ xs) = xs

zeros ∷ Stream Nat
zeros = Cons 0 (tail zeros)

filter ∷ (a → Bool) → Stream a → Stream a
filter p (Cons a xs) = if p a then Cons a (filter p xs) else filter p xs

from ∷ Nat → Stream Nat
from n = Cons n (from (Succ n))

alter ∷ Stream Bool
alter = Cons True (Cons False alter)
