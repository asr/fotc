------------------------------------------------------------------------------
-- Arithmetic properties (using induction on the LTC natural numbers)
------------------------------------------------------------------------------

module LTC.Data.Nat.PropertiesByInduction where

open import LTC.Minimal

open import LTC.Data.Nat

------------------------------------------------------------------------------

-- Usually our proofs use pattern matching instead of the induction
-- principle associated with the LTC natural numbers. The following
-- example shows a proof using it.
+-assoc : {m n o : D} → N m → N n → N o → (m + n) + o ≡ m + (n + o)
+-assoc {m} {n} {o} Nm Nn No = indN P P0 iStep Nm
  where
    P : D → Set
    P i = i + n + o ≡ i + (n + o)

    postulate
      P0 : zero + n + o ≡ zero + (n + o)
    {-# ATP prove P0 #-} -- We use the ATP systems to prove the base case.

    postulate
      iStep : {i : D} → N i →
              i + n + o ≡ i + (n + o) → -- IH.
              succ i + n + o ≡ succ i + (n + o)
    {-# ATP prove iStep #-} -- We use the ATP systems to prove the
                            -- induction step.
