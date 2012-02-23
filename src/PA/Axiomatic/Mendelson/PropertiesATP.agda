------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Axiomatic.Mendelson.PropertiesATP where

open import PA.Axiomatic.Mendelson.Base

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≐ n
+-rightIdentity = S₉ P P0 is
  where
  P : M → Set
  P i = i + zero ≐ i
  {-# ATP definition P #-}

  P0 : P zero
  P0 = S₅ zero

  postulate is : ∀ i → P i → P (succ i)
  {-# ATP prove is #-}

x+Sy≐S[x+y] : ∀ m n → m + succ n ≐ succ (m + n)
x+Sy≐S[x+y] m n = S₉ P P0 is m
  where
  P : M → Set
  P i = i + succ n ≐ succ (i + n)
  {-# ATP definition P #-}

  postulate P0 : P zero
  {-# ATP prove P0 #-}

  postulate is : ∀ i → P i → P (succ i)
  {-# ATP prove is #-}

+-leftCong : ∀ {m n o} → m ≐ n → m + o ≐ n + o
+-leftCong {m} {n} {o} h = S₉ P P0 is o
  where
  P : M → Set
  P i = m + i ≐ n + i
  {-# ATP definition P #-}

  postulate P0 : P zero
  {-# ATP prove P0 +-rightIdentity #-}

  postulate is : ∀ i → P i → P (succ i)
  {-# ATP prove is x+Sy≐S[x+y] #-}

+-asocc : ∀ m n o → m + n + o ≐ m + (n + o)
+-asocc m n o = S₉ P P0 is m
  where
  P : M → Set
  P i = i + n + o ≐ i + (n + o)
  {-# ATP definition P #-}

  postulate P0 : P zero
  {-# ATP prove P0 +-leftCong #-}

  -- 2012-02-23: Only Equinox 5.0alpha (2010-06-29) proved the theorem (180 sec).
  postulate is : ∀ i → P i → P (succ i)
  {-# ATP prove is +-leftCong #-}

+-comm : ∀ m n → m + n ≐ n + m
+-comm m n = S₉ P P0 is m
  where
  P : M → Set
  P i = i + n ≐ n + i
  {-# ATP definition P #-}

  postulate P0 : P zero
  {-# ATP prove P0 +-rightIdentity #-}

  postulate is : ∀ i → P i → P (succ i)
  {-# ATP prove is x+Sy≐S[x+y] #-}
