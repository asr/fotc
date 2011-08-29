------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

module PA.Axiomatic.PropertiesATP where

open import PA.Axiomatic.Base

open import PA.Axiomatic.Relation.Binary.PropositionalEqualityI
  using ()  -- We include this module due to its general hints.

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≣ n
+-rightIdentity = S₉ P P0 is
  where
  P : ℕ → Set
  P i = i + zero ≣ i
  {-# ATP definition P #-}

  P0 : P zero
  P0 = S₅ zero

  postulate
    is : ∀ i → P i → P (succ i)
  {-# ATP prove is #-}

x+Sy≣S[x+y] : ∀ m n → m + succ n ≣ succ (m + n)
x+Sy≣S[x+y] m n = S₉ P P0 is m
  where
  P : ℕ → Set
  P i = i + succ n ≣ succ (i + n)
  {-# ATP definition P #-}

  postulate
    P0 : P zero
  -- E 1.2: CPU time limit exceeded (180 sec).
  {-# ATP prove P0 #-}

  postulate
    is : ∀ i → P i → P (succ i)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove is #-}

+-comm : ∀ m n → m + n ≣ n + m
+-comm m n = S₉ P P0 is m
  where
  P : ℕ → Set
  P i = i + n ≣ n + i
  {-# ATP definition P #-}

  postulate
    P0 : P zero
  -- E 1.2: CPU time limit exceeded (180 sec).
  {-# ATP prove P0 +-rightIdentity #-}

  postulate
    is : ∀ i → P i → P (succ i)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove is x+Sy≣S[x+y] #-}

x≣y→x+z≣y+z : ∀ {m n} o → m ≣ n → m + o ≣ n + o
x≣y→x+z≣y+z {m} {n} o m≣n = S₉ P P0 is o
  where
  P : ℕ → Set
  P i = m + i ≣ n + i
  {-# ATP definition P #-}

  postulate
    P0 : P zero
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove P0 +-rightIdentity #-}

  postulate
    is : ∀ i → P i → P (succ i)
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds)
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove is x+Sy≣S[x+y] #-}

+-asocc : ∀ m n o → m + n + o ≣ m + (n + o)
+-asocc m n o = S₉ P P0 is m
  where
  P : ℕ → Set
  P i = i + n + o ≣ i + (n + o)
  {-# ATP definition P #-}

  postulate
    P0 : P zero
  -- E 1.2: CPU time limit exceeded (180 sec).
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove P0 x≣y→x+z≣y+z #-}

  postulate
    is : ∀ i → P i → P (succ i)
  -- E 1.4: CPU time limit exceeded, terminating (180 sec).
  -- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds)
  -- Metis 2.3 (release 20110531): SZS status Unknown (using timeout 180 sec).
  -- SPASS 3.7: Ran out of time (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): Time limit (180 sec).
  -- {-# ATP prove is x≣y→x+z≣y+z #-}
