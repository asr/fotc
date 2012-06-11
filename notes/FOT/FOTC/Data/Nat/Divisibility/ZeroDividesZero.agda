------------------------------------------------------------------------------
-- In the standard library (development version on 03 May 2012),
-- zero divides zero
------------------------------------------------------------------------------

module ZeroDividesZero where

open import Data.Nat.Divisibility
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------------

0∣0 : 0 ∣ 0
0∣0 = divides 0 refl
