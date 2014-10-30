------------------------------------------------------------------------------
-- The unary numbers are LTC-PCF total natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Data.Nat.UnaryNumbers.Totality where

open import LTC-PCF.Base
open import LTC-PCF.Data.Nat.Type
open import LTC-PCF.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

0-N : N [0]
0-N = nzero

1-N : N [1]
1-N = nsucc 0-N

2-N : N [2]
2-N = nsucc 1-N
