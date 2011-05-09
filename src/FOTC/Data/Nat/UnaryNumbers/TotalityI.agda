------------------------------------------------------------------------------
-- The unary numbers are FOTC natural numbers
------------------------------------------------------------------------------

module FOTC.Data.Nat.UnaryNumbers.TotalityI where

open import FOTC.Base

open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

0-N : N zero
0-N = zN

1-N : N one
1-N = sN 0-N

2-N : N two
2-N = sN 1-N
