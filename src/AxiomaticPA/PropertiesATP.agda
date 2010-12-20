------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

module AxiomaticPA.PropertiesATP where

open import AxiomaticPA.Base

open import AxiomaticPA.Equality.Properties
  using ()  -- We include this module due to its general hints.

------------------------------------------------------------------------------

+-rightIdentity : ∀ n → n + zero ≣ n
+-rightIdentity = S₉ P P0 iStep
  where
    P : ℕ → Set
    P i = i + zero ≣ i
    {-# ATP definition P #-}

    P0 : P zero
    P0 = S₅ zero

    postulate
      iStep : ∀ i → P i → P (succ i)
    {-# ATP prove iStep #-}

x+Sy≣S[x+y] : ∀ m n → m + succ n ≣ succ (m + n)
x+Sy≣S[x+y] m n = S₉ P P0 iStep m
  where
    P : ℕ → Set
    P i = i + succ n ≣ succ (i + n)
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : ∀ i → P i → P (succ i)
    {-# ATP prove iStep #-}

+-comm : ∀ m n → m + n ≣ n + m
+-comm m n = S₉ P P0 iStep m
  where
    P : ℕ → Set
    P i = i + n ≣ n + i
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 +-rightIdentity #-}

    postulate
      iStep : ∀ i → P i → P (succ i)
    {-# ATP prove iStep x+Sy≣S[x+y] #-}

x≣y→x+z≣y+z : ∀ {m n} o → m ≣ n → m + o ≣ n + o
x≣y→x+z≣y+z {m} {n} o m≣n = S₉ P P0 iStep o
  where
    P : ℕ → Set
    P i = m + i ≣ n + i
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 +-rightIdentity #-}

    postulate
      iStep : ∀ i → P i → P (succ i)
    {-# ATP prove iStep x+Sy≣S[x+y] #-}

+-asocc : ∀ m n o → m + n + o ≣ m + (n + o)
+-asocc m n o = S₉ P P0 iStep m
  where
    P : ℕ → Set
    P i = i + n + o ≣ i + (n + o)
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 x≣y→x+z≣y+z #-}

    postulate
      iStep : ∀ i → P i → P (succ i)
    -- E 1.2:                         No-success due to timeout (180).
    -- Equinox 5.0alpha (2010-06-29): No-success due to timeout (180).
    -- Metis 2.3 (release 20101019):  No-success due to timeout (180).
    -- {-# ATP prove iStep x≣y→x+z≣y+z #-}
