------------------------------------------------------------------------------
-- The unary numbers are FOTC natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.UnaryNumbers.TotalityI where

open import FOTC.Base
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

0-N : N [0]
0-N = nzero

1-N : N [1]
1-N = nsucc 0-N

2-N : N [2]
2-N = nsucc 1-N
