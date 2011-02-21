------------------------------------------------------------------------------
-- Arithmetic properties (using induction on the FOTC natural numbers type)
------------------------------------------------------------------------------

-- Usually our proofs use pattern matching instead of the induction
-- principle associated with the FOTC natural numbers. The following
-- examples show some proofs using it.

-- TODO: We have not tested which ATPs fail on the ATP conjectures.

module FOTC.Data.Nat.PropertiesByInductionATP where

open import FOTC.Base

open import FOTC.Data.Nat

------------------------------------------------------------------------------

+-leftIdentity : ∀ {n} → N n → zero + n ≡ n
+-leftIdentity {n} _ = +-0x n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity Nn = indN P P0 iStep Nn
  where
    P : D → Set
    P i = i + zero ≡ i
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : ∀ {i} → N i → P i → P (succ i)
    {-# ATP prove iStep #-}

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} Nm Nn = indN P P0 iStep Nm
  where
    P : D → Set
    P i = N (i + n)
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : ∀ {i} → N i → P i → P (succ i)
    {-# ATP prove iStep #-}  -- Use the hint sN.

+-assoc : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} Nm Nn No = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n + o ≡ i + (n + o)
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : ∀ {i} → N i → P i → P (succ i)
    {-# ATP prove iStep #-}

-- A proof without use ATPs definitions.
+-assoc' : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc' {n = n} {o} Nm _ _ = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n + o ≡ i + (n + o)

    postulate
      P0 : zero + n + o ≡ zero + (n + o)
    {-# ATP prove P0 #-}

    postulate
      iStep : ∀ {i} → N i →
              i + n + o ≡ i + (n + o) →  -- IH.
              succ i + n + o ≡ succ i + (n + o)
    {-# ATP prove iStep #-}

x+Sy≡S[x+y] : ∀ {m n} → N m → N n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] {n = n} Nm Nn = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + succ n ≡ succ (i + n)
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : ∀ {i} → N i → P i → P (succ i)
    {-# ATP prove iStep #-}

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} Nm Nn = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n ≡ n + i
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 +-rightIdentity #-}

    postulate
      iStep : ∀ {i} → N i → P i → P (succ i)
    {-# ATP prove iStep x+Sy≡S[x+y] #-}
