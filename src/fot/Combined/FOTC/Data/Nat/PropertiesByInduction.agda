------------------------------------------------------------------------------
-- Arithmetic properties (using induction on the FOTC natural numbers type)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Usually our proofs use pattern matching instead of the induction
-- principle associated with the FOTC natural numbers. The following
-- examples show some proofs using it.

module Combined.FOTC.Data.Nat.PropertiesByInduction where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = +-0x n

-- See Issue https://github.com/asr/apia/issues/81 .
+-rightIdentityA : D → Set
+-rightIdentityA i = i + zero ≡ i
{-# ATP definition +-rightIdentityA #-}

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity Nn = N-ind +-rightIdentityA A0 is Nn
  where
  postulate A0 : +-rightIdentityA zero
  {-# ATP prove A0 #-}

  postulate is : ∀ {i} → +-rightIdentityA i → +-rightIdentityA (succ₁ i)
  {-# ATP prove is #-}

-- See Issue https://github.com/asr/apia/issues/81 .
+-NA : D → D → Set
+-NA n i = N (i + n)
{-# ATP definition +-NA #-}

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} Nm Nn = N-ind (+-NA n) A0 is Nm
  where
  postulate A0 : +-NA n zero
  {-# ATP prove A0 #-}

  postulate is : ∀ {i} → +-NA n i → +-NA n (succ₁ i)
  {-# ATP prove is #-}

-- See Issue https://github.com/asr/apia/issues/81 .
+-assocA : D → D → D → Set
+-assocA n o i = i + n + o ≡ i + (n + o)
{-# ATP definition +-assocA #-}

+-assoc : ∀ {m} → N m → ∀ n o → m + n + o ≡ m + (n + o)
+-assoc Nm n o = N-ind (+-assocA n o) A0 is Nm
  where
  postulate A0 : +-assocA n o zero
  {-# ATP prove A0 #-}

  postulate is : ∀ {i} → +-assocA n o i → +-assocA n o (succ₁ i)
  {-# ATP prove is #-}

-- A proof without use ATPs definitions.
+-assoc' : ∀ {m} → N m → ∀ n o → m + n + o ≡ m + (n + o)
+-assoc' Nm n o = N-ind A A0 is Nm
  where
  A : D → Set
  A i = i + n + o ≡ i + (n + o)

  postulate A0 : zero + n + o ≡ zero + (n + o)
  {-# ATP prove A0 #-}

  postulate is : ∀ {i} →
                 i + n + o ≡ i + (n + o) →
                 succ₁ i + n + o ≡ succ₁ i + (n + o)
  {-# ATP prove is #-}

-- See Issue https://github.com/asr/apia/issues/81 .
x+Sy≡S[x+y]A : D → D → Set
x+Sy≡S[x+y]A n i = i + succ₁ n ≡ succ₁ (i + n)
{-# ATP definition x+Sy≡S[x+y]A #-}

x+Sy≡S[x+y] : ∀ {m} → N m → ∀ n → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] Nm n = N-ind (x+Sy≡S[x+y]A n) A0 is Nm
  where
  postulate A0 : x+Sy≡S[x+y]A n zero
  {-# ATP prove A0 #-}

  postulate is : ∀ {i} → x+Sy≡S[x+y]A n i → x+Sy≡S[x+y]A n (succ₁ i)
  {-# ATP prove is #-}

-- See Issue https://github.com/asr/apia/issues/81 .
+-commA : D → D → Set
+-commA n i = i + n ≡ n + i
{-# ATP definition +-commA #-}

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} Nm Nn = N-ind (+-commA n) A0 is Nm
  where
  postulate A0 : +-commA n zero
  {-# ATP prove A0 +-rightIdentity #-}

  postulate is : ∀ {i} → +-commA n i → +-commA n (succ₁ i)
  {-# ATP prove is x+Sy≡S[x+y] #-}
