---------------------------------------------------------------------------
-- The @rec@ definition using the fixed-point combinator
---------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Rec where

open import LTC-PCF.Base

---------------------------------------------------------------------------

rech : D → D
rech r = lam (λ n → lam (λ a → lam (λ f →
             (if (iszero₁ n)
               then a
               else f · (pred₁ n) · (r · (pred₁ n) · a · f)))))

rec : D → D → D → D
rec n a f = fix rech · n · a · f
