------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module PA.Axiomatic.Mendelson.PropertiesATP where

open import PA.Axiomatic.Mendelson.Base

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≈ n
+-leftIdentity = S₅

-- See Issue https://github.com/asr/apia/issues/81 .
+-rightIdentityA : ℕ → Set
+-rightIdentityA i = i + zero ≈ i
{-# ATP definition +-rightIdentityA #-}

+-rightIdentity : ∀ n → n + zero ≈ n
+-rightIdentity = S₉ +-rightIdentityA A0 is
  where
  A0 : +-rightIdentityA zero
  A0 = +-leftIdentity zero

  postulate is : ∀ i → +-rightIdentityA i → +-rightIdentityA (succ i)
  {-# ATP prove is #-}

-- See Issue https://github.com/asr/apia/issues/81 .
x+Sy≈S[x+y]A : ℕ → ℕ → Set
x+Sy≈S[x+y]A n i = i + succ n ≈ succ (i + n)
{-# ATP definition x+Sy≈S[x+y]A #-}

x+Sy≈S[x+y] : ∀ m n → m + succ n ≈ succ (m + n)
x+Sy≈S[x+y] m n = S₉ (x+Sy≈S[x+y]A n) A0 is m
  where
  postulate A0 : x+Sy≈S[x+y]A n zero
  {-# ATP prove A0 #-}

  postulate is : ∀ i → x+Sy≈S[x+y]A n i → x+Sy≈S[x+y]A n (succ i)
  {-# ATP prove is #-}

-- See Issue https://github.com/asr/apia/issues/81 .
+-leftCongA : ℕ → ℕ → ℕ → Set
+-leftCongA m n i = m + i ≈ n + i
{-# ATP definition +-leftCongA #-}

+-leftCong : ∀ {m n o} → m ≈ n → m + o ≈ n + o
+-leftCong {m} {n} {o} h = S₉ (+-leftCongA m n) A0 is o
  where
  postulate A0 : +-leftCongA m n zero
  {-# ATP prove A0 +-rightIdentity #-}

  postulate is : ∀ i → +-leftCongA m n i → +-leftCongA m n (succ i)
  {-# ATP prove is x+Sy≈S[x+y] #-}

-- See Issue https://github.com/asr/apia/issues/81 .
+-commA : ℕ → ℕ → Set
+-commA n i = i + n ≈ n + i
{-# ATP definition +-commA #-}

+-comm : ∀ m n → m + n ≈ n + m
+-comm m n = S₉ (+-commA n) A0 is m
  where
  postulate A0 : +-commA n zero
  {-# ATP prove A0 +-rightIdentity #-}

  postulate is : ∀ i → +-commA n i → +-commA n (succ i)
  {-# ATP prove is x+Sy≈S[x+y] #-}

+-asocc : ∀ m n o → m + n + o ≈ m + (n + o)
+-asocc m n o = S₉ A A0 is m
  where
  A : ℕ → Set
  A i = i + n + o ≈ i + (n + o)
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 +-leftCong #-}

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is +-leftCong #-}
