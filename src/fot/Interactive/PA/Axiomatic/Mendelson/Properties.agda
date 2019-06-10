------------------------------------------------------------------------------
-- Axiomatic PA properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.PA.Axiomatic.Mendelson.Properties where

open import Interactive.PA.Axiomatic.Mendelson.Base
open import Interactive.PA.Axiomatic.Mendelson.Relation.Binary.EqReasoning
open import Interactive.PA.Axiomatic.Mendelson.Relation.Binary.PropositionalEquality
  using ( ≈-sym )

------------------------------------------------------------------------------

succCong : ∀ {m n} → m ≈ n → succ m ≈ succ n
succCong = S₂

+-leftIdentity : ∀ n → zero + n ≈ n
+-leftIdentity = S₅

+-rightIdentity : ∀ n → n + zero ≈ n
+-rightIdentity = S₉ A A0 is
  where
  A : ℕ → Set
  A i = i + zero ≈ i

  A0 : A zero
  A0 = +-leftIdentity zero

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + zero   ≈⟨ S₆ i zero ⟩
            succ (i + zero) ≈⟨ S₂ ih ⟩
            succ i          ∎

x+Sy≈S[x+y] : ∀ m n → m + succ n ≈ succ (m + n)
x+Sy≈S[x+y] m n = S₉ A A0 is m
  where
  A : ℕ → Set
  A i = i + succ n ≈ succ (i + n)

  A0 : A zero
  A0 = zero + succ n   ≈⟨ +-leftIdentity (succ n) ⟩
       succ n          ≈⟨ S₂ (≈-sym (+-leftIdentity n)) ⟩
       succ (zero + n) ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + succ n     ≈⟨ S₆ i (succ n) ⟩
            succ (i + succ n)   ≈⟨ S₂ ih ⟩
            succ (succ (i + n)) ≈⟨ S₂ (≈-sym (S₆ i n)) ⟩
            succ (succ i + n)   ∎

+-rightCong : ∀ {m n p} → n ≈ p → m + n ≈ m + p
+-rightCong {m} {n} {p} h = S₉ A A0 is m
  where
  A : ℕ → Set
  A i = i + n ≈ i + p

  A0 : A zero
  A0 = zero + n ≈⟨ S₅ n ⟩
       n        ≈⟨ h ⟩
       p        ≈⟨ ≈-sym (S₅ p) ⟩
       zero + p ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + n   ≈⟨ S₆ i n ⟩
            succ (i + n) ≈⟨ S₂ ih ⟩
            succ (i + p) ≈⟨ ≈-sym (S₆ i p) ⟩
            succ i + p   ∎

+-leftCong : ∀ {m n p} → m ≈ n → m + p ≈ n + p
+-leftCong {m} {n} {p} h = S₉ A A0 is p
  where
  A : ℕ → Set
  A i = m + i ≈ n + i

  A0 : A zero
  A0 = m + zero ≈⟨ +-rightIdentity m ⟩
       m        ≈⟨ h ⟩
       n        ≈⟨ ≈-sym (+-rightIdentity n) ⟩
       n + zero ∎

  is : ∀ i → A i → A (succ i)
  is i ih = m + succ i   ≈⟨ x+Sy≈S[x+y] m i ⟩
            succ (m + i) ≈⟨ S₂ ih ⟩
            succ (n + i) ≈⟨ ≈-sym (x+Sy≈S[x+y] n i) ⟩
            n + succ i   ∎

+-asocc : ∀ m n o → m + n + o ≈ m + (n + o)
+-asocc m n o = S₉ A A0 is m
  where
  A : ℕ → Set
  A i = i + n + o ≈ i + (n + o)

  A0 : A zero
  A0 = zero + n + o   ≈⟨ +-leftCong (+-leftIdentity n) ⟩
       n + o          ≈⟨ ≈-sym (+-leftIdentity (n + o)) ⟩
       zero + (n + o) ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + n + o     ≈⟨ +-leftCong (S₆ i n) ⟩
            succ (i + n) + o   ≈⟨ S₆ (i + n) o ⟩
            succ (i + n + o)   ≈⟨ S₂ ih ⟩
            succ (i + (n + o)) ≈⟨ ≈-sym (S₆ i (n + o)) ⟩
            succ i + (n + o)   ∎

+-comm : ∀ m n → m + n ≈ n + m
+-comm m n = S₉ A A0 is m
  where
  A : ℕ → Set
  A i = i + n ≈ n + i

  A0 : A zero
  A0 = zero + n   ≈⟨ +-leftIdentity n ⟩
       n          ≈⟨ ≈-sym (+-rightIdentity n) ⟩
       n + zero   ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i + n   ≈⟨ S₆ i n ⟩
            succ (i + n) ≈⟨ S₂ ih ⟩
            succ (n + i) ≈⟨ ≈-sym (x+Sy≈S[x+y] n i) ⟩
            n + succ i   ∎

*-leftZero : ∀ n → zero * n ≈ zero
*-leftZero = S₇

*-rightZero : ∀ n → n * zero ≈ zero
*-rightZero n = S₉ A A0 is n
  where
  A : ℕ → Set
  A i = i * zero ≈ zero

  A0 : A zero
  A0 = *-leftZero zero

  is : ∀ i → A i → A (succ i)
  is i ih = succ i * zero   ≈⟨ S₈ i zero ⟩
            zero + i * zero ≈⟨ +-leftIdentity (i * zero) ⟩
            i * zero        ≈⟨ ih ⟩
            zero            ∎

x*Sy≈x+[x*y] : ∀ m n → m * succ n ≈ m + m * n
x*Sy≈x+[x*y] m n = S₉ A A0 is m
  where
  A : ℕ → Set
  A i = i * succ n ≈ i + i * n

  A0 : A zero
  A0 = zero * succ n   ≈⟨ *-leftZero (succ n) ⟩
       zero            ≈⟨ ≈-sym (S₅ zero) ⟩
       zero + zero     ≈⟨ +-rightCong (≈-sym (*-leftZero n)) ⟩
       zero + zero * n ∎

  is : ∀ i → A i → A (succ i)
  is i ih =
    succ i * succ n        ≈⟨ S₈ i (succ n) ⟩
    succ n + (i * succ n)  ≈⟨ +-rightCong ih ⟩
    succ n + (i + i * n)   ≈⟨ S₆ n (i + i * n) ⟩
    succ (n + (i + i * n)) ≈⟨ succCong (≈-sym (+-asocc n i (i * n))) ⟩
    succ (n + i + (i * n)) ≈⟨ succCong (+-leftCong (+-comm n i)) ⟩
    succ (i + n + (i * n)) ≈⟨ succCong (+-asocc i n (i * n)) ⟩
    succ (i + (n + i * n)) ≈⟨ succCong (+-rightCong (≈-sym (S₈ i n))) ⟩
    succ (i + succ i * n)  ≈⟨ ≈-sym (S₆ i (succ i * n)) ⟩
    succ i + succ i * n    ∎

*-rightCong : ∀ {m n p} → n ≈ p → m * n ≈ m * p
*-rightCong {m} {n} {p} h = S₉ A A0 is m
  where
  A : ℕ → Set
  A i = i * n ≈ i * p

  A0 : A zero
  A0 = zero * n ≈⟨ *-leftZero n ⟩
       zero     ≈⟨ ≈-sym (*-leftZero p) ⟩
       zero * p ∎

  is : ∀ i → A i → A (succ i)
  is i ih = succ i * n ≈⟨ S₈ i n ⟩
            n + i * n  ≈⟨ +-rightCong ih ⟩
            n + i * p  ≈⟨ +-leftCong h ⟩
            p + i * p  ≈⟨ ≈-sym (S₈ i p) ⟩
            succ i * p ∎

*-leftCong : ∀ {m n p} → m ≈ n → m * p ≈ n * p
*-leftCong {m} {n} {p} h = S₉ A A0 is p
  where
  A : ℕ → Set
  A i = m * i ≈ n * i

  A0 : A zero
  A0 = m * zero ≈⟨ *-rightZero m ⟩
       zero     ≈⟨ ≈-sym (*-rightZero n) ⟩
       n * zero ∎

  is : ∀ i → A i → A (succ i)
  is i ih = m * succ i ≈⟨ x*Sy≈x+[x*y] m i ⟩
            m + m * i  ≈⟨ +-leftCong h ⟩
            n + m * i  ≈⟨ +-rightCong ih ⟩
            n + n * i  ≈⟨ ≈-sym (x*Sy≈x+[x*y] n i) ⟩
            n * succ i ∎
