------------------------------------------------------------------------------
-- Arithmetic properties (using induction on the LTC natural numbers type)
------------------------------------------------------------------------------

module LTC.Data.Nat.PropertiesByInduction where

open import LTC.Minimal

open import LTC.Data.Nat using ( _+_ ; indN ; N )

------------------------------------------------------------------------------
-- Usually our proofs use pattern matching instead of the induction
-- principle associated with the LTC natural numbers. The following
-- example shows a proof using it.

-- Proof without use ATPs definitions
+-assocND : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assocND {n = n} {o} Nm _ _ = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n + o ≡ i + (n + o)

    postulate
      P0 : zero + n + o ≡ zero + (n + o)
    {-# ATP prove P0 #-}  -- We use the ATP systems to prove the base case.

    postulate
      iStep : {i : D} → N i →
              i + n + o ≡ i + (n + o) → -- IH.
              succ i + n + o ≡ succ i + (n + o)
    {-# ATP prove iStep #-}  -- We use the ATP systems to prove the
                             -- induction step.

-- Proof using ATPs definitions
+-assocD : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assocD {n = n} {o} Nm _ _ = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n + o ≡ i + (n + o)
    {-# ATP definition P #-}

    postulate
      P0 : P zero
    -- Metis 2.3 (release 20100920) no-success due to timeout (180).
    {-# ATP prove P0 #-}  -- We use the ATP systems to prove the base case.

    postulate
      iStep : {i : D} → N i → P i → P (succ i)
    -- Metis 2.3 (release 20100920) no-success due to timeout (180).
    {-# ATP prove iStep #-}  -- We use the ATP systems to prove the
                             -- induction step.
