------------------------------------------------------------------------------
-- Testing Agsy using the Agda standard library
------------------------------------------------------------------------------

module AgsyTest where

open import Data.Nat

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

------------------------------------------------------------------------------

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)  -- via Agsy {-c}
+-assoc zero    n o = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

x+1+y≡1+x+y : ∀ m n → m + suc n ≡ suc (m + n)  -- via Agsy {-c}
x+1+y≡1+x+y zero    n = refl
x+1+y≡1+x+y (suc m) n = cong suc (x+1+y≡1+x+y m n)

0+x≡x+0 : ∀ x → 0 + x ≡ x + 0  -- via Agsy {-c}
0+x≡x+0 zero    = refl
0+x≡x+0 (suc n) = cong suc (0+x≡x+0 n)

+-comm : ∀ m n → m + n ≡ n + m  -- via Agsy {-c -m}
+-comm zero    n = 0+x≡x+0 n
+-comm (suc m) n =
  begin
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨ sym (x+1+y≡1+x+y n m) ⟩
    n + suc m
  ∎
