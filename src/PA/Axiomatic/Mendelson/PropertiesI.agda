------------------------------------------------------------------------------
-- Axiomatic PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Axiomatic.Mendelson.PropertiesI where

open import PA.Axiomatic.Mendelson.Base
open import PA.Axiomatic.Mendelson.Relation.Binary.EqReasoning
open import PA.Axiomatic.Mendelson.Relation.Binary.PropositionalEqualityI
  using ( ≐-sym )

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≐ n
+-rightIdentity = S₉ P P0 is
  where
  P : M → Set
  P i = i + zero ≐ i

  P0 : P zero
  P0 = S₅ zero

  is : ∀ i → P i → P (succ i)
  is i ih = succ i + zero   ≐⟨ S₆ i zero ⟩
            succ (i + zero) ≐⟨ S₂ ih ⟩
            succ i ∎

x+Sy≐S[x+y] : ∀ m n → m + succ n ≐ succ (m + n)
x+Sy≐S[x+y] m n = S₉ P P0 is m
  where
  P : M → Set
  P i = i + succ n ≐ succ (i + n)

  P0 : P zero
  P0 = zero + succ n   ≐⟨ S₅ (succ n) ⟩
       succ n          ≐⟨ S₂ (≐-sym (S₅ n)) ⟩
       succ (zero + n) ∎

  is : ∀ i → P i → P (succ i)
  is i ih = succ i + succ n     ≐⟨ S₆ i (succ n) ⟩
            succ (i + succ n)   ≐⟨ S₂ ih ⟩
            succ (succ (i + n)) ≐⟨ S₂ (≐-sym (S₆ i n)) ⟩
            succ (succ i + n) ∎

+-leftCong : ∀ {m n o} → m ≐ n → m + o ≐ n + o
+-leftCong {m} {n} {o} h = S₉ P P0 is o
  where
  P : M → Set
  P i = m + i ≐ n + i

  P0 : P zero
  P0 = m + zero ≐⟨ +-rightIdentity m ⟩
       m        ≐⟨ h ⟩
       n        ≐⟨ ≐-sym (+-rightIdentity n) ⟩
       n + zero ∎

  is : ∀ i → P i → P (succ i)
  is i ih = m + succ i   ≐⟨ x+Sy≐S[x+y] m i ⟩
            succ (m + i) ≐⟨ S₂ ih ⟩
            succ (n + i) ≐⟨ ≐-sym (x+Sy≐S[x+y] n i) ⟩
            n + succ i ∎

+-asocc : ∀ m n o → m + n + o ≐ m + (n + o)
+-asocc m n o = S₉ P P0 is m
  where
  P : M → Set
  P i = i + n + o ≐ i + (n + o)

  P0 : P zero
  P0 = zero + n + o  ≐⟨ +-leftCong (S₅ n) ⟩
       n + o         ≐⟨ ≐-sym (S₅ (n + o)) ⟩
       zero + (n + o) ∎

  is : ∀ i → P i → P (succ i)
  is i ih = succ i + n + o     ≐⟨ +-leftCong (S₆ i n) ⟩
            succ (i + n) + o   ≐⟨ S₆ (i + n) o ⟩
            succ (i + n + o)   ≐⟨ S₂ ih ⟩
            succ (i + (n + o)) ≐⟨ ≐-sym (S₆ i (n + o)) ⟩
            succ i + (n + o) ∎

+-comm : ∀ m n → m + n ≐ n + m
+-comm m n = S₉ P P0 is m
  where
  P : M → Set
  P i = i + n ≐ n + i

  P0 : P zero
  P0 = zero + n   ≐⟨ S₅ n ⟩
       n          ≐⟨ ≐-sym (+-rightIdentity n) ⟩
       n + zero ∎

  is : ∀ i → P i → P (succ i)
  is i ih = succ i + n   ≐⟨ S₆ i n ⟩
            succ (i + n) ≐⟨ S₂ ih ⟩
            succ (n + i) ≐⟨ ≐-sym (x+Sy≐S[x+y] n i) ⟩
            n + succ i ∎
