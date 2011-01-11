------------------------------------------------------------------------------
-- Arithmetic properties (using induction on the LTC natural numbers type)
------------------------------------------------------------------------------

-- Usually our proofs use pattern matching instead of the induction
-- principle associated with the LTC natural numbers. The following
-- examples show some proofs using it.

module LTC.Data.Nat.PropertiesByInductionATP where

open import LTC.Base

open import LTC.Data.Nat

------------------------------------------------------------------------------
-- Usually our proofs use pattern matching instead of the induction
-- principle associated with the LTC natural numbers. The following
-- example shows a proof using it.

+-leftIdentity : {n : D} → N n → zero + n ≡ n
+-leftIdentity {n} _ = +-0x n

+-rightIdentity : {n : D} → N n → n + zero ≡ n
+-rightIdentity Nn = indN P P0 iStep Nn
  where
    P : D → Set
    P i = i + zero ≡ i
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : {i : D} → N i → P i → P (succ i)
    {-# ATP prove iStep #-}

+-N : {m n : D} → N m → N n → N (m + n)
+-N {n = n} Nm Nn = indN P P0 iStep Nm
  where
    P : D → Set
    P i = N (i + n)
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : {i : D} → N i → P i → P (succ i)
    {-# ATP prove iStep sN #-}

+-assoc : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} Nm Nn No = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n + o ≡ i + (n + o)
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : {i : D} → N i → P i → P (succ i)
    {-# ATP prove iStep #-}

-- A proof without use ATPs definitions.
+-assoc' : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc' {n = n} {o} Nm _ _ = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n + o ≡ i + (n + o)

    postulate
      P0 : zero + n + o ≡ zero + (n + o)
    {-# ATP prove P0 #-}

    postulate
      iStep : {i : D} → N i →
              i + n + o ≡ i + (n + o) →  -- IH.
              succ i + n + o ≡ succ i + (n + o)
    {-# ATP prove iStep #-}

x+Sy≡S[x+y] : {m n : D} → N m → N n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] {n = n} Nm Nn = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + succ n ≡ succ (i + n)
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 #-}

    postulate
      iStep : {i : D} → N i → P i → P (succ i)
    {-# ATP prove iStep #-}

+-comm : {m n : D} → N m → N n → m + n ≡ n + m
+-comm {n = n} Nm Nn = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n ≡ n + i
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    {-# ATP prove P0 +-rightIdentity #-}

    postulate
      iStep : {i : D} → N i → P i → P (succ i)
    {-# ATP prove iStep x+Sy≡S[x+y] #-}

-- -- Proof without use ATPs definitions
-- +-assocND : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
-- +-assocND {n = n} {o} Nm _ _ = indN P P0 iStep Nm
--   where
--     P : D → Set
--     P i = i + n + o ≡ i + (n + o)

--     postulate
--       P0 : zero + n + o ≡ zero + (n + o)
--     {-# ATP prove P0 #-}  -- We use the ATP systems to prove the base case.

--     postulate
--       iStep : {i : D} → N i →
--               i + n + o ≡ i + (n + o) → -- IH.
--               succ i + n + o ≡ succ i + (n + o)
--     {-# ATP prove iStep #-}  -- We use the ATP systems to prove the
--                              -- induction step.

-- -- Proof using ATPs definitions
-- +-assocD : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
-- +-assocD {n = n} {o} Nm _ _ = indN P P0 iStep Nm
--   where
--     P : D → Set
--     P i = i + n + o ≡ i + (n + o)
--     {-# ATP definition P #-}

--     postulate
--       P0 : P zero
--     -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
--     {-# ATP prove P0 #-}  -- We use the ATP systems to prove the base case.

--     postulate
--       iStep : {i : D} → N i → P i → P (succ i)
--     -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
--     {-# ATP prove iStep #-}  -- We use the ATP systems to prove the
--                              -- induction step.
