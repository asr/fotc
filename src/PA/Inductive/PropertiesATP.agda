------------------------------------------------------------------------------
-- PA properties
------------------------------------------------------------------------------

module PA.Inductive.PropertiesATP where

open import PA.Inductive.Base

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

-- The PA axioms from _+_ definition (see AxiomaticPA.Base)

S₅ : ∀ n → zero + n ≡ n
S₅ n = refl
{-# ATP hint S₅ #-}

S₆ : ∀ m n → succ m + n ≡ succ (m + n)
S₆ m n = refl
{-# ATP hint S₆ #-}

-- The PA axioms from _*_ definition (see AxiomaticPA.Base)

S₇ : ∀ n → zero * n ≡ zero
S₇ n = refl
{-# ATP hint S₇ #-}

S₈ : ∀ m n → succ m * n ≡ n + m * n
S₈ m n = refl
{-# ATP hint S₈ #-}

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

x+Sy≡S[x+y] : ∀ m n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] zero n = prf
  where
    postulate prf : zero + succ n ≡ succ (zero + n)
    {-# ATP prove prf #-}

x+Sy≡S[x+y] (succ m) n = prf (x+Sy≡S[x+y] m n)
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
    {-# ATP prove prf x+Sy≡S[x+y] #-}
