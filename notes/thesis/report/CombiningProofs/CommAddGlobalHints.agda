{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module CombiningProofs.CommAddGlobalHints where

open import PA.Axiomatic.Standard.Base

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity = PA₃

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity = ℕ-ind A A0 is
  where
  A : ℕ → Set
  A i = i + zero ≡ i
  {-# ATP definition A #-}

  A0 : A zero
  A0 = +-leftIdentity zero

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is #-}

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] m n = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + succ n ≡ succ (i + n)
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 #-}

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is #-}

-- Global hints
{-# ATP hints x+Sy≡S[x+y] +-rightIdentity #-}

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = ℕ-ind A A0 is m
  where
  A : ℕ → Set
  A i = i + n ≡ n + i
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 #-}

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is #-}
