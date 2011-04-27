------------------------------------------------------------------------------
-- In the standard library (version 0.5), zero divides zero
------------------------------------------------------------------------------

module ZeroDividesZero where

open import Data.Nat.Divisibility hiding ( 0∣0 )
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

0∣0 : 0 ∣ 0
0∣0 = divides 0 refl
