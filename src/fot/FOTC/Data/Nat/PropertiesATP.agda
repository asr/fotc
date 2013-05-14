------------------------------------------------------------------------------
-- Arithmetic properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- Totality properties

pred-N : ∀ {n} → N n → N (pred₁ n)
pred-N nzero = prf
  where postulate prf : N (pred₁ zero)
        {-# ATP prove prf #-}

pred-N (nsucc {n} Nn) = prf
  where postulate prf : N (pred₁ (succ₁ n))
        {-# ATP prove prf #-}

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} nzero Nn = prf
  where postulate prf : N (zero + n)
        {-# ATP prove prf #-}
+-N {n = n} (nsucc {m} Nm) Nn = prf (+-N Nm Nn)
  where postulate prf : N (m + n) →  N (succ₁ m + n)
        {-# ATP prove prf #-}

∸-N : ∀ {m n} → N m → N n → N (m ∸ n)
∸-N {m} Nm nzero = prf
  where postulate prf : N (m ∸ zero)
        {-# ATP prove prf #-}
∸-N {m} Nm (nsucc {n} Nn) = prf (∸-N Nm Nn)
  where postulate prf : N (m ∸ n) → N (m ∸ succ₁ n)
        {-# ATP prove prf pred-N #-}

*-N : ∀ {m n} → N m → N n → N (m * n)
*-N {n = n} nzero Nn = prf
  where postulate prf : N (zero * n)
        {-# ATP prove prf #-}
*-N {n = n} (nsucc {m} Nm) Nn = prf (*-N Nm Nn)
  where postulate prf : N (m * n) → N (succ₁ m * n)
        {-# ATP prove prf +-N #-}

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

Sx≢x : ∀ {n} → N n → succ₁ n ≢ n
Sx≢x nzero h = prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}
Sx≢x (nsucc {n} Nn) h = prf (Sx≢x Nn)
  where postulate prf : succ₁ n ≢ n → ⊥
        {-# ATP prove prf #-}

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity n = +-0x n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity nzero          = +-leftIdentity zero
+-rightIdentity (nsucc {n} Nn) = prf (+-rightIdentity Nn)
   where postulate prf : n + zero ≡ n → succ₁ n + zero ≡ succ₁ n
         {-# ATP prove prf #-}

+-assoc : ∀ {m} → N m → ∀ n o → m + n + o ≡ m + (n + o)
+-assoc nzero n o = prf
  where postulate prf : zero + n + o ≡ zero + (n + o)
        {-# ATP prove prf #-}
+-assoc (nsucc {m} Nm) n o = prf (+-assoc Nm n o)
  where postulate prf : m + n + o ≡ m + (n + o) →
                        succ₁ m + n + o ≡ succ₁ m + (n + o)
        {-# ATP prove prf #-}

x+Sy≡S[x+y] : ∀ {m} → N m → ∀ n → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] nzero n = prf
  where postulate prf : zero + succ₁ n ≡ succ₁ (zero + n)
        {-# ATP prove prf #-}
x+Sy≡S[x+y] (nsucc {m} Nm) n = prf (x+Sy≡S[x+y] Nm n)
  where postulate prf : m + succ₁ n ≡ succ₁ (m + n) →
                        succ₁ m + succ₁ n ≡ succ₁ (succ₁ m + n)
        {-# ATP prove prf #-}

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} nzero Nn = prf
  where postulate prf : zero + n ≡ n + zero
        {-# ATP prove prf +-rightIdentity #-}
+-comm {n = n} (nsucc {m} Nm) Nn = prf (+-comm Nm Nn)
  where postulate prf : m + n ≡ n + m → succ₁ m + n ≡ n + succ₁ m
        {-# ATP prove prf x+Sy≡S[x+y] #-}

x+S0≡Sx : ∀ {n} → N n → n + succ₁ zero ≡ succ₁ n
x+S0≡Sx nzero          = +-leftIdentity (succ₁ zero)
x+S0≡Sx (nsucc {n} Nn) = prf (x+S0≡Sx Nn)
  where postulate prf : n + succ₁ zero ≡ succ₁ n →
                        succ₁ n + succ₁ zero ≡ succ₁ (succ₁ n)
        {-# ATP prove prf #-}

0∸x : ∀ {n} → N n → zero ∸ n ≡ zero
0∸x nzero          = ∸-x0 zero
0∸x (nsucc {n} Nn) = prf (0∸x Nn)
  where postulate prf : zero ∸ n ≡ zero → zero ∸ succ₁ n ≡ zero
        {-# ATP prove prf #-}

S∸S : ∀ {m n} → N m → N n → succ₁ m ∸ succ₁ n ≡ m ∸ n
S∸S {m} Nm nzero = prf
  where postulate prf : succ₁ m ∸ succ₁ zero ≡ m ∸ zero
        {-# ATP prove prf #-}

S∸S nzero (nsucc {n} Nn) = prf (S∸S nzero Nn)
  where postulate prf : succ₁ zero ∸ succ₁ n ≡ zero ∸ n →
                        succ₁ zero ∸ succ₁ (succ₁ n) ≡ zero ∸ succ₁ n
        {-# ATP prove prf #-}

S∸S (nsucc {m} Nm) (nsucc {n} Nn) = prf (S∸S (nsucc Nm) Nn)
  where postulate prf : succ₁ (succ₁ m) ∸ succ₁ n ≡ succ₁ m ∸ n →
                        succ₁ (succ₁ m) ∸ succ₁ (succ₁ n) ≡ succ₁ m ∸ succ₁ n
        {-# ATP prove prf #-}

x∸x≡0 : ∀ {n} → N n → n ∸ n ≡ zero
x∸x≡0 nzero          = ∸-x0 zero
x∸x≡0 (nsucc {n} Nn) = prf (x∸x≡0 Nn)
  where postulate prf : n ∸ n ≡ zero → succ₁ n ∸ succ₁ n ≡ zero
        {-# ATP prove prf S∸S #-}

Sx∸x≡S0 : ∀ {n} → N n → succ₁ n ∸ n ≡ succ₁ zero
Sx∸x≡S0 nzero =  prf
  where postulate prf : succ₁ zero ∸ zero ≡ succ₁ zero
        {-# ATP prove prf #-}
Sx∸x≡S0 (nsucc {n} Nn) = prf (Sx∸x≡S0 Nn)
  where postulate prf : succ₁ n ∸ n ≡ succ₁ zero →
                        succ₁ (succ₁ n) ∸ succ₁ n ≡ succ₁ zero
        {-# ATP prove prf S∸S #-}

[x+Sy]∸y≡Sx : ∀ {m n} → N m → N n → (m + succ₁ n) ∸ n ≡ succ₁ m
[x+Sy]∸y≡Sx {n = n} nzero Nn = prf
  where postulate prf : zero + succ₁ n ∸ n ≡ succ₁ zero
        {-# ATP prove prf Sx∸x≡S0 #-}
[x+Sy]∸y≡Sx (nsucc {m} Nm) nzero = prf
  where postulate prf : succ₁ m + succ₁ zero ∸ zero ≡ succ₁ (succ₁ m)
        {-# ATP prove prf x+S0≡Sx #-}

[x+Sy]∸y≡Sx (nsucc {m} Nm) (nsucc {n} Nn) = prf ([x+Sy]∸y≡Sx (nsucc Nm) Nn)
  where postulate prf : succ₁ m + succ₁ n ∸ n ≡ succ₁ (succ₁ m) →
                        succ₁ m + succ₁ (succ₁ n) ∸ succ₁ n ≡ succ₁ (succ₁ m)
        {-# ATP prove prf S∸S +-N x+Sy≡S[x+y] #-}

[x+y]∸[x+z]≡y∸z : ∀ {m n o} → N m → N n → N o → (m + n) ∸ (m + o) ≡ n ∸ o
[x+y]∸[x+z]≡y∸z {n = n} {o} nzero Nn No = prf
  where postulate prf : (zero + n) ∸ (zero + o) ≡ n ∸ o
        {-# ATP prove prf #-}

[x+y]∸[x+z]≡y∸z {n = n} {o} (nsucc {m} Nm) Nn No = prf ([x+y]∸[x+z]≡y∸z Nm Nn No)
  where postulate prf : (m + n) ∸ (m + o) ≡ n ∸ o →
                        (succ₁ m + n) ∸ (succ₁ m + o) ≡ n ∸ o
        {-# ATP prove prf +-N S∸S #-}

*-leftZero : ∀ n → zero * n ≡ zero
*-leftZero = *-0x

*-rightZero : ∀ {n} → N n → n * zero ≡ zero
*-rightZero nzero          = *-leftZero zero
*-rightZero (nsucc {n} Nn) = prf (*-rightZero Nn)
  where postulate prf : n * zero ≡ zero → succ₁ n * zero ≡ zero
        {-# ATP prove prf #-}

postulate *-leftIdentity : ∀ {n} → N n → succ₁ zero * n ≡ n
{-# ATP prove *-leftIdentity +-rightIdentity #-}

x*Sy≡x+xy : ∀ {m n} → N m → N n → m * succ₁ n ≡ m + m * n
x*Sy≡x+xy {n = n} nzero Nn = prf
  where postulate prf : zero * succ₁ n ≡ zero + zero * n
        {-# ATP prove prf #-}
x*Sy≡x+xy {n = n} (nsucc {m} Nm) Nn = prf (x*Sy≡x+xy Nm Nn)
                                       (+-assoc Nn m (m * n))
                                       (+-assoc Nm n (m * n))
  where
  -- N.B. We had to feed the ATP with the instances of the associate law
  postulate prf :  m * succ₁ n ≡ m + m * n →
                   (n + m) + (m * n) ≡ n + (m + (m * n)) →  -- Associative law
                   (m + n) + (m * n) ≡ m + (n + (m * n)) →  -- Associateve law
                   succ₁ m * succ₁ n ≡ succ₁ m + succ₁ m * n
  {-# ATP prove prf +-comm #-}

*-comm : ∀ {m n} → N m → N n → m * n ≡ n * m
*-comm {n = n} nzero Nn = prf
  where postulate prf : zero * n ≡ n * zero
        {-# ATP prove prf *-rightZero #-}
*-comm {n = n} (nsucc {m} Nm) Nn = prf (*-comm Nm Nn)
  where postulate prf : m * n ≡ n * m → succ₁ m * n ≡ n * succ₁ m
        {-# ATP prove prf x*Sy≡x+xy #-}

*-rightIdentity : ∀ {n} → N n → n * succ₁ zero ≡ n
*-rightIdentity nzero = prf
  where postulate prf : zero * succ₁ zero ≡ zero
        {-# ATP prove prf #-}
*-rightIdentity (nsucc {n} Nn) = prf (*-rightIdentity Nn)
  where postulate prf : n * succ₁ zero ≡ n →
                        succ₁ n * succ₁ zero ≡ succ₁ n
        {-# ATP prove prf #-}

*∸-leftDistributive : ∀ {m n o} → N m → N n → N o → (m ∸ n) * o ≡ m * o ∸ n * o
*∸-leftDistributive {m} {o = o} Nm nzero No = prf
  where postulate prf : (m ∸ zero) * o ≡ m * o ∸ zero * o
        {-# ATP prove prf #-}

*∸-leftDistributive {o = o} nzero (nsucc {n} Nn) No = prf
  where postulate prf : (zero ∸ succ₁ n) * o ≡ zero * o ∸ succ₁ n * o
        {-# ATP prove prf 0∸x *-N #-}

*∸-leftDistributive (nsucc {m} Nm) (nsucc {n} Nn) nzero = prf
  where
  postulate prf : (succ₁ m ∸ succ₁ n) * zero ≡ succ₁ m * zero ∸ succ₁ n * zero
  {-# ATP prove prf ∸-N *-comm #-}

*∸-leftDistributive (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) =
  prf (*∸-leftDistributive Nm Nn (nsucc No))
  where
  postulate prf : (m ∸ n) * succ₁ o ≡ m * succ₁ o ∸ n * succ₁ o →
                  (succ₁ m ∸ succ₁ n) * succ₁ o ≡
                  succ₁ m * succ₁ o ∸ succ₁ n * succ₁ o
  {-# ATP prove prf [x+y]∸[x+z]≡y∸z S∸S *-N #-}

*+-leftDistributive : ∀ {m n o} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
*+-leftDistributive {m} {n} Nm Nn nzero = prf
  where postulate prf : (m + n) * zero ≡ m * zero + n * zero
        {-# ATP prove prf *-comm +-rightIdentity *-N +-N #-}

*+-leftDistributive {n = n} nzero Nn (nsucc {o} No) = prf
  where postulate prf :  (zero + n) * succ₁ o ≡ zero * succ₁ o + n * succ₁ o
        {-# ATP prove prf #-}

*+-leftDistributive (nsucc {m} Nm) nzero (nsucc {o} No) = prf
  where
  postulate prf : (succ₁ m + zero) * succ₁ o ≡ succ₁ m * succ₁ o + zero * succ₁ o
  {-# ATP prove prf +-rightIdentity *-N #-}

*+-leftDistributive (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) =
  prf (*+-leftDistributive Nm (nsucc Nn) (nsucc No))
  where
  postulate
    prf : (m + succ₁ n) * succ₁ o ≡ m * succ₁ o + succ₁ n * succ₁ o →
          (succ₁ m + succ₁ n) * succ₁ o ≡ succ₁ m * succ₁ o + succ₁ n * succ₁ o
  {-# ATP prove prf +-assoc *-N #-}

xy≡0→x≡0∨y≡0 : ∀ {m n} → N m → N n → m * n ≡ zero → m ≡ zero ∨ n ≡ zero
xy≡0→x≡0∨y≡0 {n = n} nzero Nn h = prf
  where postulate prf : zero ≡ zero ∨ n ≡ zero
        {-# ATP prove prf #-}
xy≡0→x≡0∨y≡0 (nsucc {m} Nm) nzero h = prf
  where postulate prf : succ₁ m ≡ zero ∨ zero ≡ zero
        {-# ATP prove prf #-}
xy≡0→x≡0∨y≡0 (nsucc {m} Nm) (nsucc {n} Nn) SmSn≡0 = ⊥-elim (0≢S prf)
  where postulate prf : zero ≡ succ₁ (n + m * succ₁ n)
        {-# ATP prove prf #-}

xy≡1→x≡1 : ∀ {m n} → N m → N n → m * n ≡ [1] → m ≡ [1]
xy≡1→x≡1 {n = n} nzero Nn h = ⊥-elim prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}
xy≡1→x≡1 (nsucc nzero) Nn h = refl
xy≡1→x≡1 (nsucc (nsucc {m} Nm)) nzero h = ⊥-elim prf
  where postulate prf : ⊥
        {-# ATP prove prf *-rightZero #-}
xy≡1→x≡1 (nsucc (nsucc {m} Nm)) (nsucc {n} Nn) h = ⊥-elim (0≢S prf)
  where postulate prf : zero ≡ succ₁ (m + n * succ₁ (succ₁ m))
        {-# ATP prove prf *-comm #-}
