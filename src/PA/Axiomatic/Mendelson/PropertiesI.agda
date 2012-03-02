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
+-rightIdentity = S₉ A A0 is
  where
  A : M → Set
  A i = i + zero ≐ i

  A0 : A zero
  A0 = S₅ zero

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + zero   ≐⟨ S₆ i zero ⟩
            succ (i + zero) ≐⟨ S₂ ih ⟩
            succ i ∎

x+Sy≐S[x+y] : ∀ m n → m + succ n ≐ succ (m + n)
x+Sy≐S[x+y] m n = S₉ A A0 is m
  where
  A : M → Set
  A i = i + succ n ≐ succ (i + n)

  A0 : A zero
  A0 = zero + succ n   ≐⟨ S₅ (succ n) ⟩
       succ n          ≐⟨ S₂ (≐-sym (S₅ n)) ⟩
       succ (zero + n) ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + succ n     ≐⟨ S₆ i (succ n) ⟩
            succ (i + succ n)   ≐⟨ S₂ ih ⟩
            succ (succ (i + n)) ≐⟨ S₂ (≐-sym (S₆ i n)) ⟩
            succ (succ i + n) ∎

+-leftCong : ∀ {m n o} → m ≐ n → m + o ≐ n + o
+-leftCong {m} {n} {o} h = S₉ A A0 is o
  where
  A : M → Set
  A i = m + i ≐ n + i

  A0 : A zero
  A0 = m + zero ≐⟨ +-rightIdentity m ⟩
       m        ≐⟨ h ⟩
       n        ≐⟨ ≐-sym (+-rightIdentity n) ⟩
       n + zero ∎

  is : ∀ i → A i → A (succ i)
  is i ih = m + succ i   ≐⟨ x+Sy≐S[x+y] m i ⟩
            succ (m + i) ≐⟨ S₂ ih ⟩
            succ (n + i) ≐⟨ ≐-sym (x+Sy≐S[x+y] n i) ⟩
            n + succ i ∎

+-asocc : ∀ m n o → m + n + o ≐ m + (n + o)
+-asocc m n o = S₉ A A0 is m
  where
  A : M → Set
  A i = i + n + o ≐ i + (n + o)

  A0 : A zero
  A0 = zero + n + o  ≐⟨ +-leftCong (S₅ n) ⟩
       n + o         ≐⟨ ≐-sym (S₅ (n + o)) ⟩
       zero + (n + o) ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + n + o     ≐⟨ +-leftCong (S₆ i n) ⟩
            succ (i + n) + o   ≐⟨ S₆ (i + n) o ⟩
            succ (i + n + o)   ≐⟨ S₂ ih ⟩
            succ (i + (n + o)) ≐⟨ ≐-sym (S₆ i (n + o)) ⟩
            succ i + (n + o) ∎

+-comm : ∀ m n → m + n ≐ n + m
+-comm m n = S₉ A A0 is m
  where
  A : M → Set
  A i = i + n ≐ n + i

  A0 : A zero
  A0 = zero + n   ≐⟨ S₅ n ⟩
       n          ≐⟨ ≐-sym (+-rightIdentity n) ⟩
       n + zero ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + n   ≐⟨ S₆ i n ⟩
            succ (i + n) ≐⟨ S₂ ih ⟩
            succ (n + i) ≐⟨ ≐-sym (x+Sy≐S[x+y] n i) ⟩
            n + succ i ∎
