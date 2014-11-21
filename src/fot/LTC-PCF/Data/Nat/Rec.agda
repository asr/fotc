---------------------------------------------------------------------------
-- The rec definition using the fixed-point combinator
---------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Data.Nat.Rec where

open import LTC-PCF.Base

---------------------------------------------------------------------------

-- Let T = D → D → (D → D → D) → D be a type. Instead of defining
-- rec : T → T, we use the LTC-PCF λ-abstraction and application to
-- avoid use a polymorphic fixed-point operator.

rech : D → D
rech r = lam (λ n → lam (λ a → lam (λ f →
           if (iszero₁ n)
             then a
             else f · pred₁ n · (r · pred₁ n · a · f))))

rec : D → D → D → D
rec n a f = fix rech · n · a · f
