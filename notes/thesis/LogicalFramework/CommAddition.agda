------------------------------------------------------------------------------
-- A Peano arithmetic proof without using a where clause
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LogicalFramework.CommAddition where

open import Common.FOL.Relation.Binary.EqReasoning

open import PA.Axiomatic.Standard.Base

------------------------------------------------------------------------------

postulate
  +-rightIdentity : ∀ n → n + zero ≡ n
  x+Sy≡S[x+y]     : ∀ m n → m + succ n ≡ succ (m + n)
  succCong        : ∀ {m n} → m ≡ n → succ m ≡ succ n

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity = PA₃

A : M → Set
A m = ∀ n → m + n ≡ n + m

A0 : A zero
A0 n = zero + n   ≡⟨ +-leftIdentity n ⟩
       n          ≡⟨ sym (+-rightIdentity n) ⟩
       n + zero   ∎

is : ∀ m → A m → A (succ m)
is m ih n = succ m + n   ≡⟨ PA₄ m n ⟩
            succ (m + n) ≡⟨ succCong (ih n) ⟩
            succ (n + m) ≡⟨ sym (x+Sy≡S[x+y] n m) ⟩
            n + succ m   ∎

+-comm : ∀ m n → m + n ≡ n + m
+-comm = PA-ind A A0 is
