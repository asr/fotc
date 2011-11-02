------------------------------------------------------------------------------
-- Arithmetic properties on total natural numbers
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.PropertiesATP where

open import LTC-PCF.Base

open import Common.Function

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Rec.EquationsATP

------------------------------------------------------------------------------

postulate +-0x : ∀ d → zero + d ≡ d
{-# ATP prove +-0x rec-0 #-}

postulate +-Sx : ∀ d e → succ₁ d + e ≡ succ₁ (d + e)
{-# ATP prove +-Sx rec-S #-}

postulate ∸-x0 : ∀ d → d ∸ zero ≡ d
-- E 1.2: CPU time limit exceeded (180 sec).
{-# ATP prove ∸-x0 rec-0 #-}

∸-0S : ∀ {n} → N n → zero ∸ succ₁ n ≡ zero
∸-0S zN = prf
  where
  postulate prf : zero ∸ succ₁ zero ≡ zero
  {-# ATP prove prf rec-0 #-}

∸-0S (sN {n} Nn) = prf
  where
  postulate prf : zero ∸ succ₁ (succ₁ n) ≡ zero
  {-# ATP prove prf ∸-0S rec-S #-}

∸-0x : ∀ {n} → N n → zero ∸ n ≡ zero
∸-0x zN      = ∸-x0 zero
∸-0x (sN Nn) = ∸-0S Nn

∸-SS : ∀ {m n} → N m → N n → succ₁ m ∸ succ₁ n ≡ m ∸ n
∸-SS {m} Nm zN = prf
  where
  postulate prf : succ₁ m ∸ succ₁ zero ≡ m ∸ zero
  -- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
  {-# ATP prove prf rec-S ∸-x0 #-}

∸-SS zN (sN {n} Nn) = prf $ ∸-SS zN Nn
  where
  postulate prf : succ₁ zero ∸ succ₁ n ≡ zero ∸ n →  -- IH.
                  succ₁ zero ∸ succ₁ (succ₁ n) ≡ zero ∸ succ₁ n
  {-# ATP prove prf rec-S ∸-0x ∸-0S #-}

∸-SS (sN {m} Nm) (sN {n} Nn) = prf $ ∸-SS (sN Nm) Nn
  where
  postulate prf : succ₁ (succ₁ m) ∸ succ₁ n ≡ succ₁ m ∸ n →  -- IH.
                  succ₁ (succ₁ m) ∸ succ₁ (succ₁ n) ≡ succ₁ m ∸ succ₁ n
  -- Equinox 5.0alpha (2010-06-29): TIMEOUT (180 seconds).
  {-# ATP prove prf rec-S #-}

postulate *-0x : ∀ d → zero * d ≡ zero
{-# ATP prove *-0x rec-0 #-}

postulate *-Sx : ∀ d e → succ₁ d * e ≡ e + (d * e)
{-# ATP prove *-Sx rec-S #-}

------------------------------------------------------------------------------
-- Totality properties

∸-N : ∀ {m n} → N m → N n → N (m ∸ n)
∸-N {m} Nm zN = prf
  where
  postulate prf : N (m ∸ zero)
  {-# ATP prove prf ∸-x0 #-}

∸-N zN (sN {n} Nn) = prf
  where
  postulate prf : N (zero ∸ succ₁ n)
  {-# ATP prove prf ∸-0S #-}

∸-N (sN {m} Nm) (sN {n} Nn) = prf $ ∸-N Nm Nn
  where
  postulate prf : N (m ∸ n) →  -- IH.
                  N (succ₁ m ∸ succ₁ n)
  {-# ATP prove prf ∸-SS #-}

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} zN Nn = prf
  where
  postulate prf : N (zero + n)
  {-# ATP prove prf +-0x #-}
+-N {n = n} (sN {m} Nm) Nn = prf $ +-N Nm Nn
  where
  postulate prf : N (m + n) →  -- IH.
                  N (succ₁ m + n)
  {-# ATP prove prf +-Sx #-}

*-N : ∀ {m n} → N m → N n → N (m * n)
*-N {n = n} zN Nn = prf
  where
  postulate prf : N (zero * n)
  {-# ATP prove prf *-0x #-}
*-N {n = n} (sN {m} Nm) Nn = prf $ *-N Nm Nn
  where
  postulate prf : N (m * n) →  -- IH.
                  N (succ₁ m * n)
  {-# ATP prove prf +-N *-Sx #-}

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = +-0x n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity zN          = +-leftIdentity zero
+-rightIdentity (sN {n} Nn) = prf $ +-rightIdentity Nn
   where
   postulate prf : n + zero ≡ n →  -- IH.
                   succ₁ n + zero ≡ succ₁ n
   {-# ATP prove prf +-Sx #-}

+-assoc : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} zN Nn No = prf
  where
  postulate prf : zero + n + o ≡ zero + (n + o)
  {-# ATP prove prf +-0x #-}
+-assoc {n = n} {o} (sN {m} Nm) Nn No = prf $ +-assoc Nm Nn No
  where
  postulate prf : m + n + o ≡ m + (n + o) →  -- IH.
                  succ₁ m + n + o ≡ succ₁ m + (n + o)
  {-# ATP prove prf +-Sx #-}

x+Sy≡S[x+y] : ∀ {m} n → N m → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] n zN = prf
  where
  postulate prf : zero + succ₁ n ≡ succ₁ (zero + n)
  {-# ATP prove prf +-0x #-}
x+Sy≡S[x+y] n (sN {m} Nm) = prf $ x+Sy≡S[x+y] n Nm
  where
  postulate prf : m + succ₁ n ≡ succ₁ (m + n) →  -- IH.
                  succ₁ m + succ₁ n ≡ succ₁ (succ₁ m + n)
  {-# ATP prove prf +-Sx #-}

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} zN Nn = prf
  where
    postulate prf : zero + n ≡ n + zero
    {-# ATP prove prf +-rightIdentity +-0x #-}
+-comm {n = n} (sN {m} Nm) Nn = prf $ +-comm Nm Nn
  where
  postulate prf : m + n ≡ n + m →  -- IH.
                  succ₁ m + n ≡ n + succ₁ m
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf x+Sy≡S[x+y] +-Sx #-}

[x+y]∸[x+z]≡y∸z : ∀ {m n o} → N m → N n → N o → (m + n) ∸ (m + o) ≡ n ∸ o
[x+y]∸[x+z]≡y∸z {n = n} {o} zN Nn No = prf
  where
  postulate prf : (zero + n) ∸ (zero + o) ≡ n ∸ o
  {-# ATP prove prf +-0x #-}

-- Nice proof by the ATP.
[x+y]∸[x+z]≡y∸z {n = n} {o} (sN {m} Nm) Nn No =
  prf $ [x+y]∸[x+z]≡y∸z Nm Nn No
  where
  postulate prf : (m + n) ∸ (m + o) ≡ n ∸ o →  -- IH.
                  (succ₁ m + n) ∸ (succ₁ m + o) ≡ n ∸ o
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf +-Sx ∸-SS +-N #-}

*-leftZero : ∀ n → zero * n ≡ zero
*-leftZero = *-0x

*-rightZero : ∀ {n} → N n → n * zero ≡ zero
*-rightZero zN          = *-leftZero zero
*-rightZero (sN {n} Nn) = prf $ *-rightZero Nn
  where
  postulate prf : n * zero ≡ zero →  -- IH.
                  succ₁ n * zero ≡ zero
  {-# ATP prove prf +-0x *-Sx #-}

postulate *-leftIdentity : ∀ {n} → N n → succ₁ zero * n ≡ n
{-# ATP prove *-leftIdentity +-rightIdentity *-0x *-Sx #-}

x*Sy≡x+xy : ∀ {m n} → N m → N n → m * succ₁ n ≡ m + m * n
x*Sy≡x+xy {n = n} zN Nn = prf
  where
  postulate prf : zero * succ₁ n ≡ zero + zero * n
  {-# ATP prove prf +-0x *-0x #-}
x*Sy≡x+xy {n = n} (sN {m} Nm) Nn = prf (x*Sy≡x+xy Nm Nn)
                                       (+-assoc Nn Nm (*-N Nm Nn))
                                       (+-assoc Nm Nn (*-N Nm Nn))
  where
  -- N.B. We had to feed the ATP with the instances of the associate law
  postulate prf :  m * succ₁ n ≡ m + m * n →  -- IH
                   (n + m) + (m * n) ≡ n + (m + (m * n)) →  -- Associative law
                   (m + n) + (m * n) ≡ m + (n + (m * n)) →  -- Associateve law
                   succ₁ m * succ₁ n ≡ succ₁ m + succ₁ m * n
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf +-comm +-Sx *-Sx #-}

*-comm : ∀ {m n} → N m → N n → m * n ≡ n * m
*-comm {n = n} zN Nn = prf
  where
  postulate prf : zero * n ≡ n * zero
  {-# ATP prove prf *-rightZero *-0x #-}
*-comm {n = n} (sN {m} Nm) Nn = prf $ *-comm Nm Nn
  where
  postulate prf : m * n ≡ n * m →  -- IH.
                  succ₁ m * n ≡ n * succ₁ m
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf x*Sy≡x+xy *-Sx #-}

*∸-leftDistributive : ∀ {m n o} → N m → N n → N o → (m ∸ n) * o ≡ m * o ∸ n * o
*∸-leftDistributive {m} {o = o} Nm zN No = prf
  where
  postulate prf : (m ∸ zero) * o ≡ m * o ∸ zero * o
  {-# ATP prove prf *-0x ∸-x0 #-}

*∸-leftDistributive {o = o} zN (sN {n} Nn) No = prf $ ∸-0x (*-N (sN Nn) No)
  where
  postulate prf : zero ∸ succ₁ n * o ≡ zero →
                  (zero ∸ succ₁ n) * o ≡ zero * o ∸ succ₁ n * o
  {-# ATP prove prf *-0x ∸-0S ∸-0x #-}

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) zN = prf
  where
  postulate prf : (succ₁ m ∸ succ₁ n) * zero ≡ succ₁ m * zero ∸ succ₁ n * zero
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf *-comm ∸-N sN +-0x *-0x *-Sx ∸-0x *-N #-}

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  prf $ *∸-leftDistributive Nm Nn (sN No)
  where
  postulate prf : (m ∸ n) * succ₁ o ≡ m * succ₁ o ∸ n * succ₁ o →  -- IH
                  (succ₁ m ∸ succ₁ n) * succ₁ o ≡
                  succ₁ m * succ₁ o ∸ succ₁ n * succ₁ o
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf *-N [x+y]∸[x+z]≡y∸z *-Sx ∸-SS #-}

*+-leftDistributive : ∀ {m n o} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
*+-leftDistributive {m} {n} Nm Nn zN = prf
  where
  postulate prf : (m + n) * zero ≡ m * zero + n * zero
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  {-# ATP prove prf *-comm +-rightIdentity *-N +-N *-0x #-}

*+-leftDistributive {n = n} zN Nn (sN {o} No) = prf
  where
  postulate prf :  (zero + n) * succ₁ o ≡ zero * succ₁ o + n * succ₁ o
  {-# ATP prove prf +-0x *-0x #-}

*+-leftDistributive (sN {m} Nm) zN (sN {o} Nn) = prf
  where
  postulate prf : (succ₁ m + zero) * succ₁ o ≡ succ₁ m * succ₁ o + zero * succ₁ o
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-succ₁ess (using timeout 180 sec).
  {-# ATP prove prf +-rightIdentity *-leftZero *-N #-}

*+-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  prf $ *+-leftDistributive Nm (sN Nn) (sN No)
  where
  postulate
    prf : (m + succ₁ n) * succ₁ o ≡ m * succ₁ o + succ₁ n * succ₁ o →  -- IH.
          (succ₁ m + succ₁ n) * succ₁ o ≡ succ₁ m * succ₁ o + succ₁ n * succ₁ o
  -- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
  -- Vampire 0.6 (revision 903): No-success (using timeout 180 sec).
  {-# ATP prove prf +-assoc *-N +-Sx *-Sx #-}
