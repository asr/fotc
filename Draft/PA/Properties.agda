------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

module Draft.PA.Properties where

open import Draft.PA.Base

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity = S₅

+-rightIdentity : ∀ n → n + zero ≡ n
+-rightIdentity zero     = S₅ zero
+-rightIdentity (succ n) = prf (+-rightIdentity n)
  where
    postulate prf : n + zero ≡ n →  -- IH.
                    succ n + zero ≡ succ n
    {-# ATP prove prf #-}

+-assoc : ∀ m n o → m + n + o ≡ m + (n + o)
+-assoc zero n o = prf
  where
    postulate prf : zero + n + o ≡ zero + (n + o)
    {-# ATP prove prf #-}

+-assoc (succ m) n o = prf (+-assoc m n o)
  where
    postulate prf : m + n + o ≡ m + (n + o) →  -- IH.
                    succ m + n + o ≡ succ m + (n + o)
    {-# ATP prove prf #-}

x+1+y≡1+x+y : ∀ m n → m + succ n ≡ succ (m + n)
x+1+y≡1+x+y zero n = prf
  where
    postulate prf : zero + succ n ≡ succ (zero + n)
    {-# ATP prove prf #-}

x+1+y≡1+x+y (succ m) n = prf (x+1+y≡1+x+y m n)
  where
    postulate prf : m + succ n ≡ succ (m + n) →  -- IH.
                    succ m + succ n ≡ succ (succ m + n)
    {-# ATP prove prf #-}

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero n = prf
  where
    postulate prf : zero + n ≡ n + zero
    {-# ATP prove prf +-rightIdentity #-}

+-comm (succ m) n = prf (+-comm m n)
  where
    postulate prf : m + n ≡ n + m →  -- IH.
                    succ m + n ≡ n + succ m
    {-# ATP prove prf x+1+y≡1+x+y #-}
