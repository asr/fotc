------------------------------------------------------------------------------
-- A Peano arithmetic proof without using a where clause
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with FOT on 24 February 2012.

module AdditionComm where

open import FOL.Relation.Binary.EqReasoning

open import PA.Axiomatic.Standard.Base

------------------------------------------------------------------------------

postulate
  +-rightIdentity : ∀ n → n + zero ≡ n
  x+Sy≡S[x+y]     : ∀ m n → m + succ n ≡ succ (m + n)
  succ-cong       : ∀ {m n} → m ≡ n → succ m ≡ succ n

P : M → Set
P m = ∀ n → m + n ≡ n + m

P0 : P zero
P0 n = zero + n   ≡⟨ A₃ n ⟩
       n          ≡⟨ sym (+-rightIdentity n) ⟩
       n + zero ∎

is : ∀ m → P m → P (succ m)
is m ih n = succ m + n   ≡⟨ A₄ m n ⟩
            succ (m + n) ≡⟨ succ-cong (ih n) ⟩
            succ (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
            n + succ m ∎

+-comm : ∀ m n → m + n ≡ n + m
+-comm = PA-ind P P0 is
