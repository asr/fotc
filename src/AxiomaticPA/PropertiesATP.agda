------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

module AxiomaticPA.PropertiesATP where

open import AxiomaticPA.Base
-- We include this module due to its general hints.
open import AxiomaticPA.Equality.Properties using ()

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

x+1+y≣1+x+y : ∀ m n → m + succ n ≣ succ (m + n)
x+1+y≣1+x+y m n = S₉ P P0 iStep m
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
    {-# ATP prove iStep x+1+y≣1+x+y #-}
