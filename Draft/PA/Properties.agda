------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

module Draft.PA.Properties where

open import Draft.PA.Base

open import Draft.PA.Type
  using ( N ; sN ; zN  -- The PA natural numbers type.
        )

open import Common.Function using ( _$_ )

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

+-leftIdentity : ∀ {n} → N n → zero + n ≡ n
+-leftIdentity {n} _ = S₅ n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity zN          = +-leftIdentity zN
+-rightIdentity (sN {n} Nn) = prf $ +-rightIdentity Nn
   where
     postulate prf : n + zero ≡ n →  -- IH.
                     succ n + zero ≡ succ n
     {-# ATP prove prf #-}

x+1+y≡1+x+y : ∀ {m n} → N m → N n → m + succ n ≡ succ (m + n)
x+1+y≡1+x+y {n = n} zN _ = prf
  where
    postulate prf : zero + succ n ≡ succ (zero + n)
    {-# ATP prove prf #-}
x+1+y≡1+x+y {n = n} (sN {m} Nm) Nn = prf $ x+1+y≡1+x+y Nm Nn
  where
    postulate prf : m + succ n ≡ succ (m + n) →  -- IH.
                    succ m + succ n ≡ succ (succ m + n)
    {-# ATP prove prf #-}

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} zN _ = prf
  where
    postulate prf : zero + n ≡ n + zero
    {-# ATP prove prf +-rightIdentity #-}
+-comm {n = n} (sN {m} Nm) Nn = prf $ +-comm Nm Nn
  where
    postulate prf : m + n ≡ n + m → succ m + n ≡ n + succ m
    -- Metis 2.3 (release 20101019) no-success due to timeout (180 sec).
    {-# ATP prove prf x+1+y≡1+x+y #-}
