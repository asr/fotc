------------------------------------------------------------------------------
-- Unary naturales numbers
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.LTC-PCF.Data.Nat.UnaryNumbers where

open import Interactive.LTC-PCF.Base

------------------------------------------------------------------------------

[0]  = zero
[1]  = succ₁ [0]
[2]  = succ₁ [1]
[3]  = succ₁ [2]
[4]  = succ₁ [3]
[5]  = succ₁ [4]
[6]  = succ₁ [5]
[7]  = succ₁ [6]
[8]  = succ₁ [7]
[9]  = succ₁ [8]
