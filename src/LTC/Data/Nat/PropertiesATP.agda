------------------------------------------------------------------------------
-- Arithmetic properties
------------------------------------------------------------------------------

module LTC.Data.Nat.PropertiesATP where

open import LTC.Base

open import Common.Function

open import LTC.Data.Nat

------------------------------------------------------------------------------
-- Closure properties

pred-N : ∀ {n} → N n → N (pred n)
pred-N zN  = prf
  where
    postulate prf : N (pred zero)
    {-# ATP prove prf #-}  -- Use the hint zN.

pred-N (sN {n} Nn) = prf
  where
    postulate prf : N (pred (succ n))
    {-# ATP prove prf #-}

∸-N : ∀ {m n} → N m → N n → N (m ∸ n)
∸-N {m} _ zN = prf
  where
    postulate prf : N (m ∸ zero)
    {-# ATP prove prf #-}

∸-N zN (sN {n} _) = prf
  where
    postulate prf : N (zero ∸ succ n)
    {-# ATP prove prf #-}  -- Use the hint zN.

∸-N (sN {m} Nm) (sN {n} Nn) = prf $ ∸-N Nm Nn
  where
    postulate prf : N (m ∸ n) →  -- IH.
                    N (succ m ∸ succ n)
    {-# ATP prove prf #-}

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} zN _ = prf
  where
    postulate prf : N (zero + n)
    {-# ATP prove prf #-}
+-N {n = n} (sN {m} Nm) Nn = prf $ +-N Nm Nn
  where
    postulate prf : N (m + n) →  -- IH.
                    N (succ m + n)
    {-# ATP prove prf #-}  -- Use the hint sN.

*-N : ∀ {m n} → N m → N n → N (m * n)
*-N {n = n} zN _ = prf
  where
    postulate prf : N (zero * n)
    {-# ATP prove prf #-}  -- Use the hint zN.
*-N {n = n} (sN {m} Nm) Nn = prf $ *-N Nm Nn
  where
    postulate prf : N (m * n) →  -- IH.
                    N (succ m * n)
    {-# ATP prove prf +-N #-}

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

+-leftIdentity : ∀ {n} → N n → zero + n ≡ n
+-leftIdentity {n} _ = +-0x n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity zN          = +-leftIdentity zN
+-rightIdentity (sN {n} Nn) = prf $ +-rightIdentity Nn
   where
     postulate prf : n + zero ≡ n →  -- IH.
                     succ n + zero ≡ succ n
     {-# ATP prove prf #-}

+-assoc : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} zN _ _ = prf
  where
    postulate prf : zero + n + o ≡ zero + (n + o)
    {-# ATP prove prf #-}
+-assoc {n = n} {o} (sN {m} Nm) Nn No = prf $ +-assoc Nm Nn No
  where
    postulate prf : m + n + o ≡ m + (n + o) →  -- IH.
                    succ m + n + o ≡ succ m + (n + o)
    {-# ATP prove prf #-}

x+Sy≡S[x+y] : ∀ {m n} → N m → N n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] {n = n} zN _ = prf
  where
    postulate prf : zero + succ n ≡ succ (zero + n)
    {-# ATP prove prf #-}
x+Sy≡S[x+y] {n = n} (sN {m} Nm) Nn = prf $ x+Sy≡S[x+y] Nm Nn
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
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    {-# ATP prove prf x+Sy≡S[x+y] #-}

x+S0≡Sx : ∀ {n} → N n → n + succ zero ≡ succ n
x+S0≡Sx zN          = +-0x (succ zero)
x+S0≡Sx (sN {n} Nn) = prf (x+S0≡Sx Nn)
  where
    postulate prf : n + succ zero ≡ succ n →  -- IH.
                    succ n + succ zero ≡ succ (succ n)
    {-# ATP prove prf #-}

∸-0x : ∀ {n} → N n → zero ∸ n ≡ zero
∸-0x zN         = ∸-x0 zero
∸-0x (sN {n} _) = ∸-0S n

Sx∸x≡S0 : ∀ {n} → N n → succ n ∸ n ≡ succ zero
Sx∸x≡S0 zN          = ∸-x0 (succ zero)
Sx∸x≡S0 (sN {n} Nn) = trans (∸-SS (succ n) n) (Sx∸x≡S0 Nn)

[x+Sy]∸y≡Sx : ∀ {m n} → N m → N n → (m + succ n) ∸ n ≡ succ m
[x+Sy]∸y≡Sx {n = n} zN Nn = prf
  where
    postulate prf : zero + succ n ∸ n ≡ succ zero
    {-# ATP prove prf Sx∸x≡S0 #-}
[x+Sy]∸y≡Sx (sN {m} Nm) zN = prf
  where
    postulate prf : succ m + succ zero ∸ zero ≡ succ (succ m)
    {-# ATP prove prf x+S0≡Sx #-}

[x+Sy]∸y≡Sx (sN {m} Nm) (sN {n} Nn) = prf ([x+Sy]∸y≡Sx (sN Nm) Nn)
  where
    postulate prf : succ m + succ n ∸ n ≡ succ (succ m) →  -- IH.
                    succ m + succ (succ n) ∸ succ n ≡ succ (succ m)
    {-# ATP prove prf +-comm #-}

[x+y]∸[x+z]≡y∸z : ∀ {m n o} → N m → N n → N o → (m + n) ∸ (m + o) ≡ n ∸ o
[x+y]∸[x+z]≡y∸z {n = n} {o} zN _ _ = prf
  where
    postulate prf : (zero + n) ∸ (zero + o) ≡ n ∸ o
    {-# ATP prove prf #-}

-- Nice proof by the ATP.
[x+y]∸[x+z]≡y∸z {n = n} {o} (sN {m} Nm) Nn No =
  prf $ [x+y]∸[x+z]≡y∸z Nm Nn No
  where
    postulate prf : (m + n) ∸ (m + o) ≡ n ∸ o →  -- IH.
                    (succ m + n) ∸ (succ m + o) ≡ n ∸ o
    {-# ATP prove prf #-}

*-leftZero : ∀ n → zero * n ≡ zero
*-leftZero = *-0x

*-rightZero : ∀ {n} → N n → n * zero ≡ zero
*-rightZero zN          = *-leftZero zero
*-rightZero (sN {n} Nn) = prf $ *-rightZero Nn
  where
    postulate prf : n * zero ≡ zero →  -- IH.
                    succ n * zero ≡ zero
    {-# ATP prove prf #-}

postulate *-leftIdentity : ∀ {n} → N n → succ zero * n ≡ n
{-# ATP prove *-leftIdentity +-rightIdentity #-}

x*Sy≡x+xy : ∀ {m n} → N m → N n → m * succ n ≡ m + m * n
x*Sy≡x+xy {n = n} zN _ = prf
  where
    postulate prf : zero * succ n ≡ zero + zero * n
    {-# ATP prove prf #-}
x*Sy≡x+xy {n = n} (sN {m} Nm) Nn = prf (x*Sy≡x+xy Nm Nn)
                                       (+-assoc Nn Nm (*-N Nm Nn))
                                       (+-assoc Nm Nn (*-N Nm Nn))
  where
    -- N.B. We had to feed the ATP with the instances of the associate law
    postulate prf :  m * succ n ≡ m + m * n →  -- IH
                     (n + m) + (m * n) ≡ n + (m + (m * n)) →  -- Associative law
                     (m + n) + (m * n) ≡ m + (n + (m * n)) →  -- Associateve law
                     succ m * succ n ≡ succ m + succ m * n
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    {-# ATP prove prf +-comm #-}

*-comm : ∀ {m n} → N m → N n → m * n ≡ n * m
*-comm {n = n} zN _ = prf
  where
    postulate prf : zero * n ≡ n * zero
    {-# ATP prove prf *-rightZero #-}
*-comm {n = n} (sN {m} Nm) Nn = prf $ *-comm Nm Nn
  where
    postulate prf : m * n ≡ n * m →  -- IH.
                    succ m * n ≡ n * succ m
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    {-# ATP prove prf x*Sy≡x+xy #-}

*∸-leftDistributive : ∀ {m n o} → N m → N n → N o → (m ∸ n) * o ≡ m * o ∸ n * o
*∸-leftDistributive {m} {o = o} _ zN _ = prf
  where
    postulate prf : (m ∸ zero) * o ≡ m * o ∸ zero * o
    {-# ATP prove prf #-}

*∸-leftDistributive {o = o} zN (sN {n} Nn) No = prf $ ∸-0x (*-N (sN Nn) No)
  where
    postulate prf : zero ∸ succ n * o ≡ zero →
                    (zero ∸ succ n) * o ≡ zero * o ∸ succ n * o
    {-# ATP prove prf #-}

*∸-leftDistributive (sN {m} _) (sN {n} _) zN = prf
  where
    postulate prf : (succ m ∸ succ n) * zero ≡ succ m * zero ∸ succ n * zero
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    {-# ATP prove prf ∸-N *-comm #-}  -- Use the hint zN.

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  prf $ *∸-leftDistributive Nm Nn (sN No)
  where
    postulate prf : (m ∸ n) * succ o ≡ m * succ o ∸ n * succ o →  -- IH
                    (succ m ∸ succ n) * succ o ≡
                    succ m * succ o ∸ succ n * succ o
    -- E 1.2: CPU time limit exceeded (180 sec).
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
    {-# ATP prove prf *-N [x+y]∸[x+z]≡y∸z #-}  -- Use the hint sN.

*+-leftDistributive : ∀ {m n o} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
*+-leftDistributive {m} {n} _ _ zN = prf
  where
    postulate prf : (m + n) * zero ≡ m * zero + n * zero
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
    {-# ATP prove prf *-comm +-rightIdentity *-N +-N #-}  -- Use the hints zN and sN.

*+-leftDistributive {n = n} zN _ (sN {o} _) = prf
  where
    postulate prf :  (zero + n) * succ o ≡ zero * succ o + n * succ o
    {-# ATP prove prf #-}

*+-leftDistributive (sN {m} _) zN (sN {o} _) = prf
  where
    postulate prf : (succ m + zero) * succ o ≡ succ m * succ o + zero * succ o
    -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
      -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
    {-# ATP prove prf +-rightIdentity *-leftZero *-N #-}  -- Use the hint sN.

*+-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  prf $ *+-leftDistributive Nm (sN Nn) (sN No)
    where
      postulate
        prf : (m + succ n) * succ o ≡ m * succ o + succ n * succ o →  -- IH.
              (succ m + succ n) * succ o ≡ succ m * succ o + succ n * succ o
      -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
      -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
      {-# ATP prove prf +-assoc *-N #-}  -- Use the hint sN.
