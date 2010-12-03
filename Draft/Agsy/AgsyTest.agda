------------------------------------------------------------------------------
-- Testing Agsy using the Agda standard library
------------------------------------------------------------------------------

module AgsyTest where

open import Data.Nat

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

------------------------------------------------------------------------------

0+m≡m+0 : ∀ m → 0 + m ≡ m + 0  -- via Agsy {-c}
0+m≡m+0 zero    = refl
0+m≡m+0 (suc n) = cong suc (0+m≡m+0 n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    zero    = refl -- via Agsy
+-comm zero    (suc n) = sym (cong suc (+-comm n zero))  -- via Agsy
+-comm (suc m) zero    = sym (cong suc (+-comm zero m))  -- via Agsy
+-comm (suc m) (suc n) = {!-t 20!} -- Agsy: No solution found at time out (20s)
