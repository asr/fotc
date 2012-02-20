------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PA.Axiomatic.Standard.PropertiesATP where

open import PA.Axiomatic.Standard.Base

------------------------------------------------------------------------------
-- Congruence properties

postulate succ-cong : ∀ {m n} → m ≡ n → succ m ≡ succ n
{-# ATP prove succ-cong #-}

postulate +-leftCong : ∀ {m n o} → m ≡ n → m + o ≡ n + o
{-# ATP prove +-leftCong #-}

postulate +-rightCong : ∀ {m n o} → n ≡ o → m + n ≡ m + o
{-# ATP prove +-rightCong #-}

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity = A₇ P P0 is
  where
  P : M → Set
  P i = i + zero ≡ i
  {-# ATP definition P #-}

  P0 : P zero
  P0 = A₃ zero

  postulate
    is : ∀ i → P i → P (succ i)
  {-# ATP prove is #-}

+-asocc : ∀ m n o → m + n + o ≡ m + (n + o)
+-asocc m n o = A₇ P P0 is m
  where
  P : M → Set
  P i = i + n + o ≡ i + (n + o)
  {-# ATP definition P #-}

  postulate
    P0 : P zero
  {-# ATP prove P0 #-}

  postulate
    is : ∀ i → P i → P (succ i)
  {-# ATP prove is #-}

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] m n = A₇ P P0 is m
  where
  P : M → Set
  P i = i + succ n ≡ succ (i + n)
  {-# ATP definition P #-}

  postulate
    P0 : P zero
  {-# ATP prove P0 #-}

  postulate
    is : ∀ i → P i → P (succ i)
  {-# ATP prove is #-}

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = A₇ P P0 is m
  where
  P : M → Set
  P i = i + n ≡ n + i
  {-# ATP definition P #-}

  postulate
    P0 : P zero
  {-# ATP prove P0 +-rightIdentity #-}

  postulate
    is : ∀ i → P i → P (succ i)
  {-# ATP prove is x+Sy≡S[x+y] #-}
