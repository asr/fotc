------------------------------------------------------------------------------
-- The the power function
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.FOTC.Data.Nat.Pow where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------

infixr 11 _^_

postulate
  _^_ : D → D → D
  ^-0 : ∀ n → n ^ zero      ≡ 1'
  ^-S : ∀ m n → m ^ succ₁ n ≡ m * m ^ n
{-# ATP axioms ^-0 ^-S #-}
