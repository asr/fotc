------------------------------------------------------------------------------
-- Inductive PA arithmetic properties using Agsy
------------------------------------------------------------------------------

module Agsy.PA.Inductive.Properties where

open import Data.Nat

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≡ n  -- via Agsy {-c}
+-rightIdentity zero    = refl
+-rightIdentity (suc n) = cong suc (+-rightIdentity n)

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)  -- via Agsy {-c}
+-assoc zero    n o = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

x+Sy≡S[x+y] : ∀ m n → m + suc n ≡ suc (m + n)  -- via Agsy {-c}
x+Sy≡S[x+y] zero    n = refl
x+Sy≡S[x+y] (suc m) n = cong suc (x+Sy≡S[x+y] m n)

+-comm : ∀ m n → m + n ≡ n + m  -- via Agsy {-c -m}
+-comm zero    n = sym (+-rightIdentity n)
+-comm (suc m) n =
  begin
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
    n + suc m
  ∎
