------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

module PA.Properties where

open import PA.Base

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity = S₅

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity = S₉ P P0 iStep
  where
    P : ℕ → Set
    P i = i + zero ≡ i

    P0 : zero + zero ≡ zero
    P0 = S₅ zero

    postulate
      iStep : ∀ i →
              i + zero ≡ i →
              succ i + zero ≡ succ i
    {-# ATP prove iStep #-}

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc m n o = S₉ P P0 iStep m
  where
    P : ℕ → Set
    P i = i + n + o ≡ i + (n + o)

    postulate
      P0 : zero + n + o ≡ zero + (n + o)
    {-# ATP prove P0 #-}

    postulate
      iStep : ∀ i →
              i + n + o ≡ i + (n + o) →
              succ i + n + o ≡ succ i + (n + o)
    {-# ATP prove iStep #-}

x+1+y≡1+x+y : ∀ m n → m + succ n ≡ succ (m + n)
x+1+y≡1+x+y m n = S₉ P P0 iStep m
  where
    P : ℕ → Set
    P i = i + succ n ≡ succ (i + n)

    postulate
      P0 : zero + succ n ≡ succ (zero + n)
    {-# ATP prove P0 #-}

    postulate
      iStep : ∀ i →
              i + succ n ≡ succ (i + n) →
              succ i + succ n ≡ succ (succ i + n)
    {-# ATP prove iStep #-}

+-comm : ∀ m n → m + n ≡ n + m
+-comm m n = S₉ P P0 iStep m
  where
    P : ℕ → Set
    P i = i + n ≡ n + i

    postulate
      P0 : zero + n ≡ n + zero
    {-# ATP prove P0 +-rightIdentity #-}

    postulate
      iStep : ∀ i →
              i + n ≡ n + i →
              succ i + n ≡ n + succ i
    {-# ATP prove iStep x+1+y≡1+x+y #-}
