------------------------------------------------------------------------------
-- Arithmetic properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.PropertiesATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- Congruence properties

postulate +-leftCong : ∀ {m n o} → m ≡ n → m + o ≡ n + o
{-# ATP prove +-leftCong #-}

postulate +-rightCong : ∀ {m n o} → n ≡ o → m + n ≡ m + o
{-# ATP prove +-rightCong #-}

postulate *-leftCong : ∀ {m n o} → m ≡ n → m * o ≡ n * o
{-# ATP prove *-leftCong #-}

postulate *-rightCong : ∀ {m n o} → n ≡ o → m * n ≡ m * o
{-# ATP prove *-rightCong #-}

------------------------------------------------------------------------------
-- Totality properties

-- We removed the equation pred zero ≡ zero, so we cannot prove the
-- totality of the function pred.
-- pred-N : ∀ {n} → N n → N (pred n)
-- pred-N zN  = prf
--   where
--   postulate prf : N (pred zero)
--   {-# ATP prove prf #-}

-- pred-N (sN {n} Nn) = prf
--   where
--   postulate prf : N (pred (succ n))
--   {-# ATP prove prf #-}

∸-N : ∀ {m n} → N m → N n → N (m ∸ n)
∸-N {m} Nm zN = prf
  where
  postulate prf : N (m ∸ zero)
  {-# ATP prove prf #-}

∸-N zN (sN {n} Nn) = prf
  where
  postulate prf : N (zero ∸ succ₁ n)
  {-# ATP prove prf #-}

∸-N (sN {m} Nm) (sN {n} Nn) = prf $ ∸-N Nm Nn
  where
  postulate prf : N (m ∸ n) →  -- IH.
                  N (succ₁ m ∸ succ₁ n)
  {-# ATP prove prf #-}

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} zN Nn = prf
  where
  postulate prf : N (zero + n)
  {-# ATP prove prf #-}
+-N {n = n} (sN {m} Nm) Nn = prf $ +-N Nm Nn
  where
  postulate prf : N (m + n) →  -- IH.
                  N (succ₁ m + n)
  {-# ATP prove prf #-}

*-N : ∀ {m n} → N m → N n → N (m * n)
*-N {n = n} zN Nn = prf
  where
  postulate prf : N (zero * n)
  {-# ATP prove prf #-}
*-N {n = n} (sN {m} Nm) Nn = prf $ *-N Nm Nn
  where
  postulate prf : N (m * n) →  -- IH.
                  N (succ₁ m * n)
  {-# ATP prove prf +-N #-}

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
   {-# ATP prove prf #-}

+-assoc : ∀ {m} → N m → ∀ n o → m + n + o ≡ m + (n + o)
+-assoc zN n o = prf
  where
  postulate prf : zero + n + o ≡ zero + (n + o)
  {-# ATP prove prf #-}
+-assoc (sN {m} Nm) n o = prf $ +-assoc Nm n o
  where
  postulate prf : m + n + o ≡ m + (n + o) →  -- IH.
                  succ₁ m + n + o ≡ succ₁ m + (n + o)
  {-# ATP prove prf #-}

x+Sy≡S[x+y] : ∀ {m} → N m → ∀ n → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] zN n = prf
  where
  postulate prf : zero + succ₁ n ≡ succ₁ (zero + n)
  {-# ATP prove prf #-}
x+Sy≡S[x+y] (sN {m} Nm) n = prf $ x+Sy≡S[x+y] Nm n
  where
  postulate prf : m + succ₁ n ≡ succ₁ (m + n) →  -- IH.
                  succ₁ m + succ₁ n ≡ succ₁ (succ₁ m + n)
  {-# ATP prove prf #-}

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} zN Nn = prf
  where
  postulate prf : zero + n ≡ n + zero
  {-# ATP prove prf +-rightIdentity #-}
+-comm {n = n} (sN {m} Nm) Nn = prf $ +-comm Nm Nn
  where
  postulate prf : m + n ≡ n + m → succ₁ m + n ≡ n + succ₁ m
  {-# ATP prove prf x+Sy≡S[x+y] #-}

x+S0≡Sx : ∀ {n} → N n → n + succ₁ zero ≡ succ₁ n
x+S0≡Sx zN          = +-0x (succ₁ zero)
x+S0≡Sx (sN {n} Nn) = prf (x+S0≡Sx Nn)
  where
  postulate prf : n + succ₁ zero ≡ succ₁ n →  -- IH.
                  succ₁ n + succ₁ zero ≡ succ₁ (succ₁ n)
  {-# ATP prove prf #-}

∸-0x : ∀ {n} → N n → zero ∸ n ≡ zero
∸-0x zN         = ∸-x0 zero
∸-0x (sN {n} _) = ∸-0S n

x∸x≡0 : ∀ {n} → N n → n ∸ n ≡ zero
x∸x≡0 zN          = ∸-x0 zero
x∸x≡0 (sN {n} Nn) = trans (∸-SS n n) (x∸x≡0 Nn)

Sx∸x≡S0 : ∀ {n} → N n → succ₁ n ∸ n ≡ succ₁ zero
Sx∸x≡S0 zN          = ∸-x0 (succ₁ zero)
Sx∸x≡S0 (sN {n} Nn) = trans (∸-SS (succ₁ n) n) (Sx∸x≡S0 Nn)

[x+Sy]∸y≡Sx : ∀ {m n} → N m → N n → (m + succ₁ n) ∸ n ≡ succ₁ m
[x+Sy]∸y≡Sx {n = n} zN Nn = prf
  where
  postulate prf : zero + succ₁ n ∸ n ≡ succ₁ zero
  {-# ATP prove prf Sx∸x≡S0 #-}
[x+Sy]∸y≡Sx (sN {m} Nm) zN = prf
  where
  postulate prf : succ₁ m + succ₁ zero ∸ zero ≡ succ₁ (succ₁ m)
  {-# ATP prove prf x+S0≡Sx #-}

[x+Sy]∸y≡Sx (sN {m} Nm) (sN {n} Nn) = prf ([x+Sy]∸y≡Sx (sN Nm) Nn)
  where
  postulate prf : succ₁ m + succ₁ n ∸ n ≡ succ₁ (succ₁ m) →  -- IH.
                  succ₁ m + succ₁ (succ₁ n) ∸ succ₁ n ≡ succ₁ (succ₁ m)
  {-# ATP prove prf +-comm #-}

[x+y]∸[x+z]≡y∸z : ∀ {m} → N m → ∀ n o → (m + n) ∸ (m + o) ≡ n ∸ o
[x+y]∸[x+z]≡y∸z zN n o = prf
  where
  postulate prf : (zero + n) ∸ (zero + o) ≡ n ∸ o
  {-# ATP prove prf #-}

-- Nice proof by the ATP.
[x+y]∸[x+z]≡y∸z (sN {m} Nm) n o =
  prf $ [x+y]∸[x+z]≡y∸z Nm n o
  where
  postulate prf : (m + n) ∸ (m + o) ≡ n ∸ o →  -- IH.
                  (succ₁ m + n) ∸ (succ₁ m + o) ≡ n ∸ o
  {-# ATP prove prf #-}

*-leftZero : ∀ n → zero * n ≡ zero
*-leftZero = *-0x

*-rightZero : ∀ {n} → N n → n * zero ≡ zero
*-rightZero zN          = *-leftZero zero
*-rightZero (sN {n} Nn) = prf $ *-rightZero Nn
  where
  postulate prf : n * zero ≡ zero →  -- IH.
                  succ₁ n * zero ≡ zero
  {-# ATP prove prf #-}

postulate *-leftIdentity : ∀ {n} → N n → succ₁ zero * n ≡ n
{-# ATP prove *-leftIdentity +-rightIdentity #-}

x*Sy≡x+xy : ∀ {m n} → N m → N n → m * succ₁ n ≡ m + m * n
x*Sy≡x+xy {n = n} zN Nn = prf
  where
  postulate prf : zero * succ₁ n ≡ zero + zero * n
  {-# ATP prove prf #-}
x*Sy≡x+xy {n = n} (sN {m} Nm) Nn = prf (x*Sy≡x+xy Nm Nn)
                                       (+-assoc Nn m (m * n))
                                       (+-assoc Nm n (m * n))
  where
  -- N.B. We had to feed the ATP with the instances of the associate law
  postulate prf :  m * succ₁ n ≡ m + m * n →  -- IH
                   (n + m) + (m * n) ≡ n + (m + (m * n)) →  -- Associative law
                   (m + n) + (m * n) ≡ m + (n + (m * n)) →  -- Associateve law
                   succ₁ m * succ₁ n ≡ succ₁ m + succ₁ m * n
  {-# ATP prove prf +-comm #-}

*-comm : ∀ {m n} → N m → N n → m * n ≡ n * m
*-comm {n = n} zN Nn = prf
  where
  postulate prf : zero * n ≡ n * zero
  {-# ATP prove prf *-rightZero #-}
*-comm {n = n} (sN {m} Nm) Nn = prf $ *-comm Nm Nn
  where
  postulate prf : m * n ≡ n * m →  -- IH.
                  succ₁ m * n ≡ n * succ₁ m
  {-# ATP prove prf x*Sy≡x+xy #-}

*-rightIdentity : ∀ {n} → N n → n * succ₁ zero ≡ n
*-rightIdentity {n} Nn = trans (*-comm Nn (sN zN)) (*-leftIdentity Nn)

*∸-leftDistributive : ∀ {m n o} → N m → N n → N o → (m ∸ n) * o ≡ m * o ∸ n * o
*∸-leftDistributive {m} {o = o} Nm zN No = prf
  where
  postulate prf : (m ∸ zero) * o ≡ m * o ∸ zero * o
  {-# ATP prove prf #-}

*∸-leftDistributive {o = o} zN (sN {n} Nn) No = prf $ ∸-0x (*-N (sN Nn) No)
  where
  postulate prf : zero ∸ succ₁ n * o ≡ zero →
                  (zero ∸ succ₁ n) * o ≡ zero * o ∸ succ₁ n * o
  {-# ATP prove prf #-}

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) zN = prf
  where
  postulate prf : (succ₁ m ∸ succ₁ n) * zero ≡ succ₁ m * zero ∸ succ₁ n * zero
  {-# ATP prove prf ∸-N *-comm #-}

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  prf $ *∸-leftDistributive Nm Nn (sN No)
  where
  postulate prf : (m ∸ n) * succ₁ o ≡ m * succ₁ o ∸ n * succ₁ o →  -- IH
                  (succ₁ m ∸ succ₁ n) * succ₁ o ≡
                  succ₁ m * succ₁ o ∸ succ₁ n * succ₁ o
  {-# ATP prove prf [x+y]∸[x+z]≡y∸z #-}

*+-leftDistributive : ∀ {m n o} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
*+-leftDistributive {m} {n} Nm Nn zN = prf
  where
  postulate prf : (m + n) * zero ≡ m * zero + n * zero
  {-# ATP prove prf *-comm +-rightIdentity *-N +-N #-}

*+-leftDistributive {n = n} zN Nn (sN {o} No) = prf
  where
  postulate prf :  (zero + n) * succ₁ o ≡ zero * succ₁ o + n * succ₁ o
  {-# ATP prove prf #-}

*+-leftDistributive (sN {m} Nm) zN (sN {o} No) = prf
  where
  postulate prf : (succ₁ m + zero) * succ₁ o ≡ succ₁ m * succ₁ o + zero * succ₁ o
  {-# ATP prove prf +-rightIdentity *-N #-}

*+-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  prf $ *+-leftDistributive Nm (sN Nn) (sN No)
  where
  postulate
    prf : (m + succ₁ n) * succ₁ o ≡ m * succ₁ o + succ₁ n * succ₁ o →  -- IH.
          (succ₁ m + succ₁ n) * succ₁ o ≡ succ₁ m * succ₁ o + succ₁ n * succ₁ o
  {-# ATP prove prf +-assoc *-N #-}

xy≡0→x≡0∨y≡0 : ∀ {m n} → N m → N n → m * n ≡ zero → m ≡ zero ∨ n ≡ zero
xy≡0→x≡0∨y≡0 zN      _  _                   = inj₁ refl
xy≡0→x≡0∨y≡0 (sN Nm) zN _                   = inj₂ refl
xy≡0→x≡0∨y≡0 (sN {m} Nm) (sN {n} Nn) SmSn≡0 = ⊥-elim (0≢S prf)
  where
  postulate prf : zero ≡ succ₁ (n + m * succ₁ n)
  {-# ATP prove prf #-}

xy≡1→x≡1∨y≡1 : ∀ {m n} → N m → N n → m * n ≡ one → m ≡ one ∨ n ≡ one
xy≡1→x≡1∨y≡1 {n = n} zN Nn h = ⊥-elim (0≢S (trans (sym (*-leftZero n)) h))
xy≡1→x≡1∨y≡1 (sN {m} Nm) zN h =
  ⊥-elim (0≢S (trans (sym (*-rightZero (sN Nm))) h))
xy≡1→x≡1∨y≡1 (sN zN) (sN Nn) h = inj₁ refl
xy≡1→x≡1∨y≡1 (sN (sN Nm)) (sN zN) h = inj₂ refl
xy≡1→x≡1∨y≡1 (sN (sN {m} Nm)) (sN (sN {n} Nn)) h = prf
  where
  postulate prf : succ₁ (succ₁ m) ≡ one ∨ succ₁ (succ₁ n) ≡ one
  {-# ATP prove prf #-}
