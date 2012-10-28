------------------------------------------------------------------------------
-- Arithmetic properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Rec
open import LTC-PCF.Data.Nat.Rec.Equations
open import LTC-PCF.Data.Nat.SubtractionEquations public

------------------------------------------------------------------------------
-- Congruence properties

succCong : ∀ {m n} → m ≡ n → succ₁ m ≡ succ₁ n
succCong refl = refl

predCong : ∀ {m n} → m ≡ n → pred₁ m ≡ pred₁ n
predCong refl = refl

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

+-0x : ∀ n → zero + n ≡ n
+-0x n = rec zero n _ ≡⟨ rec-0 n ⟩
         n            ∎

+-Sx : ∀ m n → succ₁ m + n ≡ succ₁ (m + n)
+-Sx m n =
  rec (succ₁ m) n (lam (λ _ → lam succ₁))
    ≡⟨ rec-S m n (lam (λ _ → lam succ₁)) ⟩
  (lam (λ _ → lam succ₁)) · m · (m + n)
    ≡⟨ ·-leftCong (beta (λ _ → lam succ₁) m) ⟩
  lam succ₁ · (m + n)
    ≡⟨ beta succ₁ (m + n) ⟩
  succ₁ (m + n) ∎

*-0x : ∀ n → zero * n ≡ zero
*-0x n = rec zero zero (lam (λ _ → lam (λ x → n + x))) ≡⟨ rec-0 zero ⟩
         zero                                          ∎

*-Sx : ∀ m n → succ₁ m * n ≡ n + m * n
*-Sx m n =
  rec (succ₁ m) zero (lam (λ _ → lam (λ x → n + x)))
    ≡⟨ rec-S m zero (lam (λ _ → lam (λ x → n + x))) ⟩
  (lam (λ _ → lam (λ x → n + x))) · m · (m * n)
    ≡⟨ ·-leftCong (beta (λ _ → lam (λ x → n + x)) m) ⟩
  lam (λ x → n + x) · (m * n)
    ≡⟨ beta (λ x → n + x) (m * n) ⟩
  n + (m * n) ∎

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity = +-0x

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity nzero          = +-leftIdentity zero
+-rightIdentity (nsucc {n} Nn) =
  trans (+-Sx n zero) (succCong (+-rightIdentity Nn))

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} nzero          Nn = subst N (sym (+-leftIdentity n)) Nn
+-N {n = n} (nsucc {m} Nm) Nn = subst N (sym (+-Sx m n)) (nsucc (+-N Nm Nn))

∸-N : ∀ {m n} → N m → N n → N (m ∸ n)
∸-N {m} Nm             nzero          = subst N (sym (∸-x0 m)) Nm
∸-N     nzero          (nsucc {n} _)  = subst N (sym (∸-0S n)) nzero
∸-N     (nsucc {m} Nm) (nsucc {n} Nn) = subst N (sym (∸-SS m n)) (∸-N Nm Nn)

+-assoc : ∀ {m} → N m →  ∀ n o → m + n + o ≡ m + (n + o)
+-assoc nzero n o =
  zero + n + o   ≡⟨ +-leftCong (+-leftIdentity n) ⟩
  n + o          ≡⟨ sym (+-leftIdentity (n + o)) ⟩
  zero + (n + o) ∎

+-assoc (nsucc {m} Nm) n o =
  succ₁ m + n + o     ≡⟨ +-leftCong (+-Sx m n) ⟩
  succ₁ (m + n) + o   ≡⟨ +-Sx (m + n) o ⟩
  succ₁ (m + n + o)   ≡⟨ succCong (+-assoc Nm n o) ⟩
  succ₁ (m + (n + o)) ≡⟨ sym (+-Sx m (n + o)) ⟩
  succ₁ m + (n + o)   ∎

x+Sy≡S[x+y] : ∀ {m} → N m → ∀ n → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] nzero n =
  zero + succ₁ n   ≡⟨ +-leftIdentity (succ₁ n) ⟩
  succ₁ n          ≡⟨ succCong (sym (+-leftIdentity n)) ⟩
  succ₁ (zero + n) ∎

x+Sy≡S[x+y] (nsucc {m} Nm) n =
  succ₁ m + succ₁ n     ≡⟨ +-Sx m (succ₁ n) ⟩
  succ₁ (m + succ₁ n)   ≡⟨ succCong (x+Sy≡S[x+y] Nm n) ⟩
  succ₁ (succ₁ (m + n)) ≡⟨ succCong (sym (+-Sx m n)) ⟩
  succ₁ (succ₁ m + n)   ∎

∸-0x : ∀ {n} → N n → zero ∸ n ≡ zero
∸-0x nzero         = ∸-x0 zero
∸-0x (nsucc {n} Nm) = ∸-0S n

[x+y]∸[x+z]≡y∸z : ∀ {m n o} → N m → N n → N o → (m + n) ∸ (m + o) ≡ n ∸ o
[x+y]∸[x+z]≡y∸z {n = n} {o} nzero _ _ =
  (zero + n) ∸ (zero + o) ≡⟨ ∸-leftCong (+-leftIdentity n) ⟩
    n ∸ (zero + o)        ≡⟨ ∸-rightCong (+-leftIdentity o) ⟩
    n ∸ o                 ∎

[x+y]∸[x+z]≡y∸z {n = n} {o} (nsucc {m} Nm) Nn No =
  (succ₁ m + n) ∸ (succ₁ m + o) ≡⟨ ∸-leftCong (+-Sx m n) ⟩
  succ₁ (m + n) ∸ (succ₁ m + o) ≡⟨ ∸-rightCong (+-Sx m o) ⟩
  succ₁ (m + n) ∸ succ₁ (m + o) ≡⟨ ∸-SS (m + n) (m + o) ⟩
  (m + n) ∸ (m + o)             ≡⟨ [x+y]∸[x+z]≡y∸z Nm Nn No ⟩
  n ∸ o                         ∎

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} nzero Nn =
  zero + n ≡⟨ +-leftIdentity n ⟩
  n        ≡⟨ sym (+-rightIdentity Nn) ⟩
  n + zero ∎

+-comm {n = n} (nsucc {m} Nm) Nn =
  succ₁ m + n   ≡⟨ +-Sx m n ⟩
  succ₁ (m + n) ≡⟨ succCong (+-comm Nm Nn) ⟩
  succ₁ (n + m) ≡⟨ sym (x+Sy≡S[x+y] Nn m) ⟩
  n + succ₁ m   ∎

*-leftZero : ∀ n → zero * n ≡ zero
*-leftZero = *-0x

*-rightZero : ∀ {n} → N n → n * zero ≡ zero
*-rightZero nzero          = *-leftZero zero
*-rightZero (nsucc {n} Nn) =
  trans (*-Sx n zero)
        (trans (+-leftIdentity (n * zero)) (*-rightZero Nn))

*-N : ∀ {m n} → N m → N n → N (m * n)
*-N {n = n} nzero          _  = subst N (sym (*-leftZero n)) nzero
*-N {n = n} (nsucc {m} Nm) Nn = subst N (sym (*-Sx m n)) (+-N Nn (*-N Nm Nn))

*-leftIdentity : ∀ {n} → N n → succ₁ zero * n ≡ n
*-leftIdentity {n} Nn =
  succ₁ zero * n ≡⟨ *-Sx zero n ⟩
  n + zero * n   ≡⟨ +-rightCong (*-leftZero n) ⟩
  n + zero       ≡⟨ +-rightIdentity Nn ⟩
  n              ∎

x*Sy≡x+xy : ∀ {m n} → N m → N n → m * succ₁ n ≡ m + m * n
x*Sy≡x+xy {n = n} nzero Nn = sym
  (
    zero + zero * n ≡⟨ +-rightCong (*-leftZero n) ⟩
    zero + zero     ≡⟨ +-leftIdentity zero ⟩
    zero            ≡⟨ sym (*-leftZero (succ₁ n)) ⟩
    zero * succ₁ n  ∎
  )

x*Sy≡x+xy {n = n} (nsucc {m} Nm) Nn =
  succ₁ m * succ₁ n
    ≡⟨ *-Sx m (succ₁ n) ⟩
  succ₁ n + m * succ₁ n
    ≡⟨ +-rightCong (x*Sy≡x+xy Nm Nn) ⟩
  succ₁ n + (m + m * n)
    ≡⟨ +-Sx n (m + m * n) ⟩
  succ₁ (n + (m + m * n))
    ≡⟨ succCong (sym (+-assoc Nn m (m * n))) ⟩
  succ₁ (n + m + m * n)
    ≡⟨ succCong (+-leftCong (+-comm Nn Nm)) ⟩
  succ₁ (m + n + m * n)
    ≡⟨ subst (λ t → succ₁ (m + n + m * n) ≡ succ₁ t)
             (+-assoc Nm n (m * n))
               refl
    ⟩
  succ₁ (m + (n + m * n))
    ≡⟨ sym (+-Sx m (n + m * n)) ⟩
  succ₁ m + (n + m * n)
    ≡⟨ +-rightCong (sym (*-Sx m n)) ⟩
  succ₁ m + succ₁ m * n ∎

*-comm : ∀ {m n} → N m → N n → m * n ≡ n * m
*-comm {n = n} nzero          Nn = trans (*-leftZero n) (sym (*-rightZero Nn))
*-comm {n = n} (nsucc {m} Nm) Nn =
  succ₁ m * n  ≡⟨ *-Sx m n ⟩
  n + m * n    ≡⟨ subst (λ t → n + m * n ≡ n + t) (*-comm Nm Nn) refl ⟩
  n + n * m    ≡⟨ sym (x*Sy≡x+xy Nn Nm) ⟩
  n * succ₁ m  ∎

*∸-leftDistributive : ∀ {m n o} → N m → N n → N o → (m ∸ n) * o ≡ m * o ∸ n * o
*∸-leftDistributive {m} {o = o} _ nzero _ =
  (m ∸ zero) * o   ≡⟨ *-leftCong (∸-x0 m) ⟩
  m * o            ≡⟨ sym (∸-x0 (m * o)) ⟩
  m * o ∸ zero     ≡⟨ ∸-rightCong (sym (*-leftZero o)) ⟩
  m * o ∸ zero * o ∎

*∸-leftDistributive {o = o} nzero (nsucc {n} Nn) No =
  (zero ∸ succ₁ n) * o   ≡⟨ *-leftCong (∸-0S n) ⟩
  zero * o               ≡⟨ *-leftZero o ⟩
  zero                   ≡⟨ sym (∸-0x (*-N (nsucc Nn) No)) ⟩
  zero ∸ succ₁ n * o     ≡⟨ ∸-leftCong (sym (*-leftZero o)) ⟩
  zero * o ∸ succ₁ n * o ∎

*∸-leftDistributive (nsucc {m} Nm) (nsucc {n} Nn) nzero =
  (succ₁ m ∸ succ₁ n) * zero
    ≡⟨ *-comm (∸-N (nsucc Nm) (nsucc Nn)) nzero ⟩
  zero * (succ₁ m ∸ succ₁ n)
    ≡⟨ *-leftZero (succ₁ m ∸ succ₁ n) ⟩
  zero
    ≡⟨ sym (∸-0x (*-N (nsucc Nn) nzero)) ⟩
  zero ∸ succ₁ n * zero
    ≡⟨ ∸-leftCong (sym (*-leftZero (succ₁ m))) ⟩
  zero * succ₁ m ∸ succ₁ n * zero
    ≡⟨ ∸-leftCong (*-comm nzero (nsucc Nm)) ⟩
  succ₁ m * zero ∸ succ₁ n * zero ∎

*∸-leftDistributive (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) =
  (succ₁ m ∸ succ₁ n) * succ₁ o
    ≡⟨ *-leftCong (∸-SS m n) ⟩
  (m ∸ n) * succ₁ o
     ≡⟨ *∸-leftDistributive Nm Nn (nsucc No) ⟩
  m * succ₁ o ∸ n * succ₁ o
    ≡⟨ sym ([x+y]∸[x+z]≡y∸z (nsucc No) (*-N Nm (nsucc No)) (*-N Nn (nsucc No))) ⟩
  (succ₁ o + m * succ₁ o) ∸ (succ₁ o + n * succ₁ o)
    ≡⟨ ∸-leftCong (sym (*-Sx m (succ₁ o))) ⟩
  (succ₁ m * succ₁ o) ∸ (succ₁ o + n * succ₁ o)
    ≡⟨ ∸-rightCong (sym (*-Sx n (succ₁ o))) ⟩
  (succ₁ m * succ₁ o) ∸ (succ₁ n * succ₁ o) ∎

*+-leftDistributive : ∀ {m n o} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
*+-leftDistributive {m} {n} Nm Nn nzero =
  (m + n) * zero
    ≡⟨ *-comm (+-N Nm Nn) nzero ⟩
  zero * (m + n)
    ≡⟨ *-leftZero (m + n) ⟩
  zero
    ≡⟨ sym (*-leftZero m) ⟩
  zero * m
    ≡⟨ *-comm nzero Nm ⟩
  m * zero
    ≡⟨ sym (+-rightIdentity (*-N Nm nzero)) ⟩
  m * zero + zero
    ≡⟨ +-rightCong (trans (sym (*-leftZero n)) (*-comm nzero Nn)) ⟩
  m * zero + n * zero ∎

*+-leftDistributive {n = n} nzero Nn (nsucc {o} No) =
  (zero + n) * succ₁ o         ≡⟨ *-leftCong (+-leftIdentity n) ⟩
  n * succ₁ o                  ≡⟨ sym (+-leftIdentity (n * succ₁ o)) ⟩
  zero + n * succ₁ o           ≡⟨ +-leftCong (sym (*-leftZero (succ₁ o))) ⟩
  zero * succ₁ o + n * succ₁ o ∎

*+-leftDistributive (nsucc {m} Nm) nzero (nsucc {o} No) =
  (succ₁ m + zero) * succ₁ o
    ≡⟨ *-leftCong (+-rightIdentity (nsucc Nm)) ⟩
  succ₁ m * succ₁ o
    ≡⟨ sym (+-rightIdentity (*-N (nsucc Nm) (nsucc No))) ⟩
  succ₁ m * succ₁ o + zero
    ≡⟨ +-rightCong (sym (*-leftZero (succ₁ o))) ⟩
  succ₁ m * succ₁ o + zero * succ₁ o ∎

*+-leftDistributive (nsucc {m} Nm) (nsucc {n} Nn) (nsucc {o} No) =
  (succ₁ m + succ₁ n) * succ₁ o
    ≡⟨ *-leftCong (+-Sx m (succ₁ n)) ⟩
  succ₁ (m + succ₁ n) * succ₁ o
    ≡⟨ *-Sx (m + succ₁ n) (succ₁ o) ⟩
  succ₁ o + (m + succ₁ n) * succ₁ o
    ≡⟨ +-rightCong (*+-leftDistributive Nm (nsucc Nn) (nsucc No)) ⟩
  succ₁ o + (m * succ₁ o + succ₁ n * succ₁ o)
    ≡⟨ sym (+-assoc (nsucc No) (m * succ₁ o) (succ₁ n * succ₁ o)) ⟩
  succ₁ o + m * succ₁ o + succ₁ n * succ₁ o
    ≡⟨ +-leftCong (sym (*-Sx m (succ₁ o))) ⟩
  succ₁ m * succ₁ o + succ₁ n * succ₁ o ∎
