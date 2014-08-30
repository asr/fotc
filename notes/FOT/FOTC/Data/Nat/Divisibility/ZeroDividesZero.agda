------------------------------------------------------------------------------
-- In the Agda standard library zero divides zero
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Nat.Divisibility.ZeroDividesZero where

open import Data.Nat.Divisibility
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

0∣0 : 0 ∣ 0
0∣0 = divides 0 refl
