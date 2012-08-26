------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Axiomatic.Mendelson.PropertiesATP where

open import PA.Axiomatic.Mendelson.Base

------------------------------------------------------------------------------

+-leftIdentity : ∀ n → zero + n ≈ n
+-leftIdentity = S₅

+-rightIdentity : ∀ n → n + zero ≈ n
+-rightIdentity = S₉ A A0 is
  where
  A : M → Set
  A i = i + zero ≈ i
  {-# ATP definition A #-}

  A0 : A zero
  A0 = +-leftIdentity zero

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is #-}

x+Sy≈S[x+y] : ∀ m n → m + succ n ≈ succ (m + n)
x+Sy≈S[x+y] m n = S₉ A A0 is m
  where
  A : M → Set
  A i = i + succ n ≈ succ (i + n)
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 #-}

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is #-}

+-leftCong : ∀ {m n o} → m ≈ n → m + o ≈ n + o
+-leftCong {m} {n} {o} h = S₉ A A0 is o
  where
  A : M → Set
  A i = m + i ≈ n + i
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 +-rightIdentity #-}

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is x+Sy≈S[x+y] #-}

+-asocc : ∀ m n o → m + n + o ≈ m + (n + o)
+-asocc m n o = S₉ A A0 is m
  where
  A : M → Set
  A i = i + n + o ≈ i + (n + o)
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 +-leftCong #-}

  -- 22 May 2012: After the addition of the inequality _≉_, no ATP
  -- proves the theorem (240 sec). Before it, only Equinox 5.0alpha
  -- (2010-06-29) had proved the theorem.
  postulate is : ∀ i → A i → A (succ i)
  -- {-# ATP prove is +-leftCong #-}

+-comm : ∀ m n → m + n ≈ n + m
+-comm m n = S₉ A A0 is m
  where
  A : M → Set
  A i = i + n ≈ n + i
  {-# ATP definition A #-}

  postulate A0 : A zero
  {-# ATP prove A0 +-rightIdentity #-}

  postulate is : ∀ i → A i → A (succ i)
  {-# ATP prove is x+Sy≈S[x+y] #-}
