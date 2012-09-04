------------------------------------------------------------------------------
-- Arithmetic properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- M. J. Beeson. Proving programs and programming proofs. In Ruth
-- Barcan Marcus, George J. W. Dorn, and Paul Weingartner,
-- editors. Logic, Methodology and Philosophy of Science VII (1983),
-- volume 114 of Studies in Logic and the Foundations of
-- Mathematics. North-Holland Publishing Company, 1988, pages 51–82.

module FOTC.Data.Nat.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning
open import Common.Function

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Nat
open import FOTC.Data.Nat.UnaryNumbers

------------------------------------------------------------------------------
-- Congruence properties

succCong : ∀ {m n} → m ≡ n → succ₁ m ≡ succ₁ n
succCong refl = refl

+-leftCong : ∀ {m n o} → m ≡ n → m + o ≡ n + o
+-leftCong refl = refl

+-rightCong : ∀ {m n o} → n ≡ o → m + n ≡ m + o
+-rightCong refl = refl

∸-leftCong : ∀ {m n o} → m ≡ n → m ∸ o ≡ n ∸ o
∸-leftCong refl = refl

∸-rightCong : ∀ {m n o} → n ≡ o → m ∸ n ≡ m ∸ o
∸-rightCong refl = refl

*-leftCong : ∀ {m n o} → m ≡ n → m * o ≡ n * o
*-leftCong refl = refl

*-rightCong : ∀ {m n o} → n ≡ o → m * n ≡ m * o
*-rightCong refl = refl

------------------------------------------------------------------------------
-- Some proofs are based on the proofs in the standard library.

Sx≢x : ∀ {n} → N n → succ₁ n ≢ n
Sx≢x nzero h      = ⊥-elim (0≢S (sym h))
Sx≢x (nsucc Nn) h = ⊥-elim (Sx≢x Nn (succInjective h))

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity = +-0x

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity nzero          = +-leftIdentity zero
+-rightIdentity (nsucc {n} Nn) =
  trans (+-Sx n zero)
        (subst (λ t → succ₁ (n + zero) ≡ succ₁ t)
               (+-rightIdentity Nn)
               refl
        )

-- We removed the equation pred zero ≡ zero, so we cannot prove the
-- totality of the function pred.
-- pred-N : ∀ {n} → N n → N (pred n)
-- pred-N nzero = subst N (sym pred-0) nzero
-- pred-N (nsucc {n} Nn) = subst N (sym $ pred-S n) Nn

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} nzero          Nn = subst N (sym $ +-leftIdentity n) Nn
+-N {n = n} (nsucc {m} Nm) Nn = subst N (sym $ +-Sx m n) (nsucc (+-N Nm Nn))

∸-N : ∀ {m n} → N m → N n → N (m ∸ n)
∸-N {m} Nm             nzero          = subst N (sym $ ∸-x0 m) Nm
∸-N     nzero          (nsucc {n} _)  = subst N (sym $ ∸-0S n) nzero
∸-N     (nsucc {m} Nm) (nsucc {n} Nn) = subst N (sym $ ∸-SS m n) (∸-N Nm Nn)

+-assoc : ∀ {m} → N m → ∀ n o → m + n + o ≡ m + (n + o)
+-assoc nzero n o =
  zero + n + o   ≡⟨ subst (λ t → zero + n + o ≡ t + o) (+-leftIdentity n) refl ⟩
  n + o          ≡⟨ sym $ +-leftIdentity (n + o) ⟩
  zero + (n + o) ∎

+-assoc (nsucc {m} Nm) n o =
  succ₁ m + n + o
    ≡⟨ subst (λ t → succ₁ m + n + o ≡ t + o) (+-Sx m n) refl ⟩
  succ₁ (m + n) + o
    ≡⟨ +-Sx (m + n) o ⟩
  succ₁ (m + n + o)
    ≡⟨ subst (λ t → succ₁ (m + n + o) ≡ succ₁ t) (+-assoc Nm n o) refl ⟩
  succ₁ (m + (n + o)) ≡⟨ sym $ +-Sx m (n + o) ⟩
  succ₁ m + (n + o) ∎

x+Sy≡S[x+y] : ∀ {m} → N m → ∀ n → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] nzero n =
  zero + succ₁ n
    ≡⟨ +-leftIdentity (succ₁ n) ⟩
  succ₁ n
    ≡⟨ subst (λ t → succ₁ n ≡ succ₁ t) (sym $ +-leftIdentity n) refl ⟩
  succ₁ (zero + n) ∎

x+Sy≡S[x+y] (nsucc {m} Nm) n =
  succ₁ m + succ₁ n
    ≡⟨ +-Sx m (succ₁ n) ⟩
  succ₁ (m + succ₁ n)
      ≡⟨ subst (λ t → succ₁ (m + succ₁ n) ≡ succ₁ t) (x+Sy≡S[x+y] Nm n) refl ⟩
  succ₁ (succ₁ (m + n))
    ≡⟨ subst (λ t → succ₁ (succ₁ (m + n)) ≡ succ₁ t) (sym $ +-Sx m n) refl ⟩
  succ₁ (succ₁ m + n) ∎

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} nzero Nn =
  zero + n ≡⟨ +-leftIdentity n ⟩
  n        ≡⟨ sym $ +-rightIdentity Nn ⟩
  n + zero ∎

+-comm {n = n} (nsucc {m} Nm) Nn =
  succ₁ m + n   ≡⟨ +-Sx m n ⟩
  succ₁ (m + n) ≡⟨ succCong (+-comm Nm Nn) ⟩
  succ₁ (n + m) ≡⟨ sym $ x+Sy≡S[x+y] Nn m ⟩
  n + succ₁ m   ∎

∸-0x : ∀ {n} → N n → zero ∸ n ≡ zero
∸-0x nzero         = ∸-x0 zero
∸-0x (nsucc {n} _) = ∸-0S n

x∸x≡0 : ∀ {n} → N n → n ∸ n ≡ zero
x∸x≡0 nzero          = ∸-x0 zero
x∸x≡0 (nsucc {n} Nn) = trans (∸-SS n n) (x∸x≡0 Nn)

Sx∸x≡S0 : ∀ {n} → N n → succ₁ n ∸ n ≡ succ₁ zero
Sx∸x≡S0 nzero          = ∸-x0 (succ₁ zero)
Sx∸x≡S0 (nsucc {n} Nn) = trans (∸-SS (succ₁ n) n) (Sx∸x≡S0 Nn)

[x+y]∸[x+z]≡y∸z : ∀ {m} → N m → ∀ n o → (m + n) ∸ (m + o) ≡ n ∸ o
[x+y]∸[x+z]≡y∸z nzero n o =
  (zero + n) ∸ (zero + o)
    ≡⟨ subst (λ t → (zero + n) ∸ (zero + o) ≡ t ∸ (zero + o))
             (+-leftIdentity n)
             refl
    ⟩
  n ∸ (zero + o)
    ≡⟨ subst (λ t → n ∸ (zero + o) ≡ n ∸ t)
             (+-leftIdentity o)
             refl
    ⟩
  n ∸ o ∎

[x+y]∸[x+z]≡y∸z (nsucc {m} Nm) n o =
  (succ₁ m + n) ∸ (succ₁ m + o)
    ≡⟨ subst (λ t → succ₁ m + n ∸ (succ₁ m + o) ≡ t ∸ (succ₁ m + o))
             (+-Sx m n)
             refl
    ⟩
  succ₁ (m + n) ∸ (succ₁ m + o)
    ≡⟨ subst (λ t → succ₁ (m + n) ∸ (succ₁ m + o) ≡ succ₁ (m + n) ∸ t)
             (+-Sx m o)
             refl
    ⟩
  succ₁ (m + n) ∸ succ₁ (m + o)
    ≡⟨ ∸-SS (m + n) (m + o) ⟩
  (m + n) ∸ (m + o)
    ≡⟨ [x+y]∸[x+z]≡y∸z Nm n o ⟩
  n ∸ o ∎

*-leftZero : ∀ n → zero * n ≡ zero
*-leftZero = *-0x

*-rightZero : ∀ {n} → N n → n * zero ≡ zero
*-rightZero nzero          = *-leftZero zero
*-rightZero (nsucc {n} Nn) =
  trans (*-Sx n zero)
        (trans (+-leftIdentity (n * zero)) (*-rightZero Nn))

*-N : ∀ {m n} → N m → N n → N (m * n)
*-N {n = n} nzero          Nn = subst N (sym $ *-leftZero n) nzero
*-N {n = n} (nsucc {m} Nm) Nn = subst N (sym $ *-Sx m n) (+-N Nn (*-N Nm Nn))

*-leftIdentity : ∀ {n} → N n → succ₁ zero * n ≡ n
*-leftIdentity {n} Nn =
  succ₁ zero * n ≡⟨ *-Sx zero n ⟩
  n + zero * n   ≡⟨ subst (λ t → n + zero * n ≡ n + t) (*-leftZero n) refl ⟩
  n + zero       ≡⟨ +-rightIdentity Nn ⟩
  n              ∎

x*Sy≡x+xy : ∀ {m n} → N m → N n → m * succ₁ n ≡ m + m * n
x*Sy≡x+xy {n = n} nzero Nn = sym
  (
    zero + zero * n
      ≡⟨ subst (λ t → zero + zero * n ≡ zero + t) (*-leftZero n) refl ⟩
    zero + zero
      ≡⟨ +-leftIdentity zero ⟩
    zero
      ≡⟨ sym $ *-leftZero (succ₁ n) ⟩
    zero * succ₁ n ∎
  )

x*Sy≡x+xy {n = n} (nsucc {m} Nm) Nn =
  succ₁ m * succ₁ n
    ≡⟨ *-Sx m (succ₁ n) ⟩
  succ₁ n + m * succ₁ n
    ≡⟨ subst (λ t → succ₁ n + m * succ₁ n ≡ succ₁ n + t)
             (x*Sy≡x+xy Nm Nn)
             refl
    ⟩
  succ₁ n + (m + m * n)
    ≡⟨ +-Sx n (m + m * n) ⟩
  succ₁ (n + (m + m * n))
    ≡⟨ subst (λ t → succ₁ (n + (m + m * n)) ≡ succ₁ t)
             (sym $ +-assoc Nn m (m * n))
             refl
    ⟩
  succ₁ (n + m + m * n)
    ≡⟨ subst (λ t → succ₁ (n + m + m * n) ≡ succ₁ (t + m * n))
             (+-comm Nn Nm)
             refl
    ⟩
  succ₁ (m + n + m * n)
    ≡⟨ subst (λ t → succ₁ (m + n + m * n) ≡ succ₁ t)
             (+-assoc Nm n (m * n))
               refl
    ⟩
  succ₁ (m + (n + m * n))
    ≡⟨ sym $ +-Sx m (n + m * n) ⟩
  succ₁ m + (n + m * n)
    ≡⟨ subst (λ t → succ₁ m + (n + m * n) ≡ succ₁ m + t)
             (sym $ *-Sx m n)
             refl
    ⟩
  succ₁ m + succ₁ m * n ∎

*-comm : ∀ {m n} → N m → N n → m * n ≡ n * m
*-comm {n = n} nzero Nn          = trans (*-leftZero n) (sym $ *-rightZero Nn)
*-comm {n = n} (nsucc {m} Nm) Nn =
  succ₁ m * n ≡⟨ *-Sx m n ⟩
  n + m * n   ≡⟨ subst (λ t → n + m * n ≡ n + t) (*-comm Nm Nn) refl ⟩
  n + n * m   ≡⟨ sym $ x*Sy≡x+xy Nn Nm ⟩
  n * succ₁ m ∎

*-rightIdentity : ∀ {n} → N n → n * succ₁ zero ≡ n
*-rightIdentity {n} Nn = trans (*-comm Nn (nsucc nzero)) (*-leftIdentity Nn)

*∸-leftDistributive : ∀ {m n o} → N m → N n → N o → (m ∸ n) * o ≡ m * o ∸ n * o
*∸-leftDistributive {m} {o = o} _ nzero _ =
  (m ∸ zero) * o
    ≡⟨ subst (λ t → (m ∸ zero) * o ≡ t * o) (∸-x0 m) refl ⟩
  m * o
    ≡⟨ sym $ ∸-x0 (m * o) ⟩
  m * o ∸ zero
    ≡⟨ subst (λ t → m * o ∸ zero ≡ m * o ∸ t)
             (sym $ *-leftZero o)
             refl
    ⟩
  m * o ∸ zero * o ∎

*∸-leftDistributive {o = o} nzero (nsucc {n} Nn) No =
  (zero ∸ succ₁ n) * o
    ≡⟨ subst (λ t → (zero ∸ succ₁ n) * o ≡ t * o) (∸-0S n) refl ⟩
  zero * o
    ≡⟨ *-leftZero o ⟩
  zero
    ≡⟨ sym $ ∸-0x (*-N (nsucc Nn) No) ⟩
  zero ∸ succ₁ n * o
    ≡⟨ subst (λ t → zero ∸ succ₁ n * o ≡ t ∸ succ₁ n * o)
             (sym $ *-leftZero o)
             refl
    ⟩
  zero * o ∸ succ₁ n * o ∎

*∸-leftDistributive (nsucc {m} Nm) (nsucc {n} Nn) nzero =
  (succ₁ m ∸ succ₁ n) * zero
    ≡⟨ *-comm (∸-N (nsucc Nm) (nsucc Nn)) nzero ⟩
  zero * (succ₁ m ∸ succ₁ n)
    ≡⟨ *-leftZero (succ₁ m ∸ succ₁ n) ⟩
  zero
    ≡⟨ sym $ ∸-0x (*-N (nsucc Nn) nzero) ⟩
  zero ∸ succ₁ n * zero
    ≡⟨ subst (λ t → zero ∸ succ₁ n * zero ≡ t ∸ succ₁ n * zero)
             (sym $ *-leftZero (succ₁ m))
             refl
    ⟩
  zero * succ₁ m ∸ succ₁ n * zero
    ≡⟨ subst (λ t → zero * succ₁ m ∸ succ₁ n * zero ≡ t ∸ succ₁ n * zero)
             (*-comm nzero (nsucc Nm))
             refl
    ⟩
  succ₁ m * zero ∸ succ₁ n * zero ∎

*∸-leftDistributive (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) =
  (succ₁ m ∸ succ₁ n) * succ₁ o
    ≡⟨ subst (λ t → (succ₁ m ∸ succ₁ n) * succ₁ o ≡ t * succ₁ o)
                    (∸-SS m n)
                    refl
    ⟩
  (m ∸ n) * succ₁ o
     ≡⟨ *∸-leftDistributive Nm Nn (nsucc No) ⟩
  m * succ₁ o ∸ n * succ₁ o
    ≡⟨ sym $ [x+y]∸[x+z]≡y∸z (nsucc No) (m * succ₁ o) (n * succ₁ o) ⟩
  (succ₁ o + m * succ₁ o) ∸ (succ₁ o + n * succ₁ o)
    ≡⟨ subst (λ t → (succ₁ o + m * succ₁ o) ∸ (succ₁ o + n * succ₁ o) ≡
                    t ∸ (succ₁ o + n * succ₁ o))
             (sym $ *-Sx m (succ₁ o))
             refl
    ⟩
  (succ₁ m * succ₁ o) ∸ (succ₁ o + n * succ₁ o)
    ≡⟨ subst (λ t → (succ₁ m * succ₁ o) ∸ (succ₁ o + n * succ₁ o) ≡
                    (succ₁ m * succ₁ o) ∸ t)
             (sym $ *-Sx n (succ₁ o))
             refl
    ⟩
  (succ₁ m * succ₁ o) ∸ (succ₁ n * succ₁ o) ∎

*+-leftDistributive : ∀ {m n o} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
*+-leftDistributive {m} {n} Nm Nn nzero =
  (m + n) * zero
    ≡⟨ *-comm (+-N Nm Nn) nzero ⟩
  zero * (m + n)
    ≡⟨ *-leftZero (m + n) ⟩
  zero
    ≡⟨ sym $ *-leftZero m ⟩
  zero * m
    ≡⟨ *-comm nzero Nm ⟩
  m * zero
    ≡⟨ sym $ +-rightIdentity (*-N Nm nzero) ⟩
  m * zero + zero
    ≡⟨ subst (λ t → m * zero + zero ≡ m * zero + t)
             (trans (sym $ *-leftZero n) (*-comm nzero Nn))
             refl
    ⟩
  m * zero + n * zero ∎

*+-leftDistributive {n = n} nzero Nn (nsucc {o} No) =
  (zero + n) * succ₁ o
    ≡⟨ subst (λ t → (zero + n) * succ₁ o ≡ t * succ₁ o)
             (+-leftIdentity n)
             refl
    ⟩
  n * succ₁ o
    ≡⟨ sym $ +-leftIdentity (n * succ₁ o) ⟩
  zero + n * succ₁ o
    ≡⟨ subst (λ t → zero + n * succ₁ o ≡ t +  n * succ₁ o)
             (sym $ *-leftZero (succ₁ o))
             refl
    ⟩
  zero * succ₁ o + n * succ₁ o ∎

*+-leftDistributive (nsucc {m} Nm) nzero (nsucc {o} No) =
  (succ₁ m + zero) * succ₁ o
    ≡⟨ subst (λ t → (succ₁ m + zero) * succ₁ o ≡ t * succ₁ o)
             (+-rightIdentity (nsucc Nm))
             refl
    ⟩
  succ₁ m * succ₁ o
    ≡⟨ sym $ +-rightIdentity (*-N (nsucc Nm) (nsucc No)) ⟩
  succ₁ m * succ₁ o + zero
    ≡⟨ subst (λ t → succ₁ m * succ₁ o + zero ≡ succ₁ m * succ₁ o + t)
             (sym $ *-leftZero (succ₁ o))
             refl
    ⟩
  succ₁ m * succ₁ o + zero * succ₁ o ∎

*+-leftDistributive (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) =
  (succ₁ m + succ₁ n) * succ₁ o
    ≡⟨ subst (λ t → (succ₁ m + succ₁ n) * succ₁ o ≡ t * succ₁ o)
             (+-Sx m (succ₁ n))
             refl
    ⟩
  succ₁ (m + succ₁ n) * succ₁ o
    ≡⟨ *-Sx (m + succ₁ n) (succ₁ o) ⟩
  succ₁ o + (m + succ₁ n) * succ₁ o
    ≡⟨ subst (λ t → succ₁ o + (m + succ₁ n) * succ₁ o ≡ succ₁ o + t)
             (*+-leftDistributive Nm (nsucc Nn) (nsucc No))
             refl
    ⟩
  succ₁ o + (m * succ₁ o + succ₁ n * succ₁ o)
    ≡⟨ sym $ +-assoc (nsucc No) (m * succ₁ o) (succ₁ n * succ₁ o) ⟩
  succ₁ o + m * succ₁ o + succ₁ n * succ₁ o
    ≡⟨ subst (λ t → succ₁ o + m * succ₁ o + succ₁ n * succ₁ o ≡
                    t + succ₁ n * succ₁ o)
             (sym $ *-Sx m (succ₁ o))
             refl
    ⟩
  succ₁ m * succ₁ o + succ₁ n * succ₁ o ∎

xy≡0→x≡0∨y≡0 : ∀ {m n} → N m → N n → m * n ≡ zero → m ≡ zero ∨ n ≡ zero
xy≡0→x≡0∨y≡0 nzero          _              _      = inj₁ refl
xy≡0→x≡0∨y≡0 (nsucc Nm)     nzero          _      = inj₂ refl
xy≡0→x≡0∨y≡0 (nsucc {m} Nm) (nsucc {n} Nn) SmSn≡0 = ⊥-elim (0≢S prf)
  where
  prf : zero ≡ succ₁ (n + m * succ₁ n)
  prf = zero                    ≡⟨ sym SmSn≡0 ⟩
        succ₁ m * succ₁ n       ≡⟨ *-Sx m (succ₁ n) ⟩
        succ₁ n + m * succ₁ n   ≡⟨ +-Sx n (m * succ₁ n) ⟩
        succ₁ (n + m * succ₁ n) ∎

xy≡1→x≡1 : ∀ {m n} → N m → N n → m * n ≡ one → m ≡ one
xy≡1→x≡1 {n = n} nzero Nn h = ⊥-elim (0≢S (trans (sym (*-leftZero n)) h))
xy≡1→x≡1 (nsucc nzero) Nn h = refl
xy≡1→x≡1 (nsucc (nsucc {m} Nm)) nzero h =
  ⊥-elim (0≢S (trans (sym (*-rightZero (nsucc (nsucc Nm)))) h))
xy≡1→x≡1 (nsucc (nsucc {m} Nm)) (nsucc {n} Nn) h = ⊥-elim (0≢S prf₂)
  where
  prf₁ : succ₁ zero ≡ succ₁ (succ₁ (m + n * succ₁ (succ₁ m)))
  prf₁ = succ₁ zero
           ≡⟨ sym h ⟩
         succ₁ (succ₁ m) * succ₁ n
           ≡⟨ *-comm (nsucc (nsucc Nm)) (nsucc Nn) ⟩
         succ₁ n * succ₁ (succ₁ m)
           ≡⟨ *-Sx n (succ₁ (succ₁ m)) ⟩
         succ₁ (succ₁ m) + n * succ₁ (succ₁ m)
           ≡⟨ +-Sx (succ₁ m) (n * succ₁ (succ₁ m)) ⟩
         succ₁ (succ₁ m + n * succ₁ (succ₁ m))
           ≡⟨ succCong (+-Sx m (n * succ₁ (succ₁ m))) ⟩
         succ₁ (succ₁ (m + n * succ₁ (succ₁ m))) ∎

  prf₂ : zero ≡ succ₁ (m + n * succ₁ (succ₁ m))
  prf₂ = succInjective prf₁

xy≡1→y≡1 : ∀ {m n} → N m → N n → m * n ≡ one → n ≡ one
xy≡1→y≡1 Nm Nn h = xy≡1→x≡1 Nn Nm (trans (*-comm Nn Nm) h)

-- Feferman's axiom as presented by (Beeson 1986, p. 74).
succOnto : ∀ {n} → N n → n ≢ zero → succ₁ (pred₁ n) ≡ n
succOnto nzero          h = ⊥-elim (h refl)
succOnto (nsucc {n} Nn) h = succCong (pred-S n)
