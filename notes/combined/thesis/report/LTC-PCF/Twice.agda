------------------------------------------------------------------------------
-- Twice funcion
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Twice where

open import Interactive.LTC-PCF.Base

------------------------------------------------------------------------------

twice : (D → D) → D → D
twice f x = f (f x)

twice-succ : ∀ n → twice succ₁ n ≡ succ₁ (succ₁ n)
twice-succ n = refl
