------------------------------------------------------------------------------
-- In the standard library zero divides zero
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of the standard library on
-- 11 June 2012.

module ZeroDividesZero where

open import Data.Nat.Divisibility
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

0∣0 : 0 ∣ 0
0∣0 = divides 0 refl
