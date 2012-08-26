------------------------------------------------------------------------------
-- Inductive PA arithmetic properties using Agsy
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of the standard library on
-- 02 February 2012.

module Agsy.PA.Inductive.Properties where

open import Data.Nat renaming (suc to succ)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≡ n  -- via Agsy {-c}
+-rightIdentity zero     = refl
+-rightIdentity (succ n) = cong succ (+-rightIdentity n)

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)  -- via Agsy {-c}
+-assoc zero     n o = refl
+-assoc (succ m) n o = cong succ (+-assoc m n o)

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)  -- via Agsy {-c}
x+Sy≡S[x+y] zero     n = refl
x+Sy≡S[x+y] (succ m) n = cong succ (x+Sy≡S[x+y] m n)

+-comm : ∀ m n → m + n ≡ n + m  -- via Agsy {-c -m}
+-comm zero    n = sym (+-rightIdentity n)
+-comm (succ m) n =
  begin
    succ (m + n) ≡⟨ cong succ (+-comm m n) ⟩
    succ (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
    n + succ m
  ∎
