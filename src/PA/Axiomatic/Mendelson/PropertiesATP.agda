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
  -- E 1.2: CPU time limit exceeded (180 sec).
  {-# ATP prove P0 #-}

  postulate is : ∀ i → P i → P (succ i)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove is #-}

+-leftCong : ∀ {m n o} → m ≐ n → m + o ≐ n + o
+-leftCong {m} {n} {o} h = S₉ P P0 is o
  where
  P : M → Set
  P i = m + i ≐ n + i
  {-# ATP definition P #-}

  postulate P0 : P zero
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove P0 +-rightIdentity #-}

  postulate is : ∀ i → P i → P (succ i)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove is x+Sy≐S[x+y] #-}

+-asocc : ∀ m n o → m + n + o ≐ m + (n + o)
+-asocc m n o = S₉ P P0 is m
  where
  P : M → Set
  P i = i + n + o ≐ i + (n + o)
  {-# ATP definition P #-}

  postulate P0 : P zero
  {-# ATP prove P0 +-leftCong #-}

  postulate is : ∀ i → P i → P (succ i)
  -- (2012-02-22) E 1.4. CPU time limit exceeded, terminating (180 sec).
  -- (2012-02-22) Metis 2.3 (release 20110926). SZS status Unknown (180 sec).
  -- (2012-02-22) Vampire 0.6 (revision 903). Time limit reached! (180 sec).
  {-# ATP prove is +-leftCong #-}

+-comm : ∀ m n → m + n ≐ n + m
+-comm m n = S₉ P P0 is m
  where
  P : M → Set
  P i = i + n ≐ n + i
  {-# ATP definition P #-}

  postulate P0 : P zero
  -- E 1.2: CPU time limit exceeded (180 sec).
  {-# ATP prove P0 +-rightIdentity #-}

  postulate is : ∀ i → P i → P (succ i)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove is x+Sy≐S[x+y] #-}
