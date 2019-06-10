------------------------------------------------------------------------------
-- The unary numbers are FOTC total natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Data.Nat.UnaryNumbers.Totality where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Data.Nat.Type
open import Interactive.FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

0-N : N 0'
0-N = nzero

1-N : N 1'
1-N = nsucc 0-N

2-N : N 2'
2-N = nsucc 1-N

3-N : N 3'
3-N = nsucc 2-N

4-N : N 4'
4-N = nsucc 3-N

5-N : N 5'
5-N = nsucc 4-N

-- TODO (2019-06-09): Missing proofs.
postulate
  10-N  : N 10'
  11-N  : N 11'
  89-N  : N 89'
  90-N  : N 90'
  91-N  : N 91'
  92-N  : N 92'
  93-N  : N 93'
  94-N  : N 94'
  95-N  : N 95'
  96-N  : N 96'
  97-N  : N 97'
  98-N  : N 98'
  99-N  : N 99'
  100-N : N 100'
  101-N : N 101'

