------------------------------------------------------------------------------
-- Arithmetic properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Rec
open import LTC-PCF.Data.Nat.Rec.EquationsI

------------------------------------------------------------------------------
-- Congruence properties

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
  rec (succ₁ m) n (lam (λ x → lam (λ y → succ₁ y)))
    ≡⟨ rec-S m n (lam (λ x → lam (λ y → succ₁ y))) ⟩
  (lam (λ x → lam (λ y → succ₁ y))) · m · (m + n)
    ≡⟨ ·-leftCong (beta (λ x → lam (λ y → succ₁ y)) m) ⟩
  (λ x → lam (λ y → succ₁ y)) m · (m + n)
    ≡⟨ refl ⟩
  lam succ₁ · (m + n)
    ≡⟨ beta succ₁ (m + n) ⟩
  succ₁ (m + n) ∎

∸-x0 : ∀ n → n ∸ zero ≡ n
∸-x0 n = rec zero n _ ≡⟨ rec-0 n ⟩
         n            ∎

∸-0S : ∀ {n} → N n → zero ∸ succ₁ n ≡ zero
∸-0S zN =
  rec (succ₁ zero) zero (lam (λ x → lam (λ y → pred₁ y)))
    ≡⟨ rec-S zero zero (lam (λ x → lam (λ y → pred₁ y))) ⟩
  lam (λ x → lam (λ y → pred₁ y)) · zero · (zero ∸ zero)
    ≡⟨ ·-leftCong (beta (λ x → lam (λ y → pred₁ y)) zero) ⟩
  (λ x → lam (λ y → pred₁ y)) zero · (zero ∸ zero)
    ≡⟨ refl ⟩
  lam pred₁ · (zero ∸ zero)
    ≡⟨ beta pred₁ (zero ∸ zero) ⟩
  pred₁ (zero ∸ zero)
    ≡⟨ cong pred₁ (∸-x0 zero) ⟩
  pred₁ zero
    ≡⟨ pred-0 ⟩
  zero ∎

∸-0S (sN {n} Nn) =
  rec (succ₁ (succ₁ n)) zero (lam (λ x → lam (λ y → pred₁ y)))
    ≡⟨ rec-S (succ₁ n) zero (lam (λ x → lam (λ y → pred₁ y))) ⟩
  lam (λ x → lam (λ y → pred₁ y)) · (succ₁ n) · (zero ∸ (succ₁ n))
    ≡⟨ ·-leftCong (beta (λ x → lam (λ y → pred₁ y)) (succ₁ n)) ⟩
  (λ x → lam (λ y → pred₁ y))  (succ₁ n) · (zero ∸ (succ₁ n))
    ≡⟨ refl ⟩
  lam pred₁ · (zero ∸ (succ₁ n))
    ≡⟨ beta pred₁ (zero ∸ (succ₁ n)) ⟩
  pred₁ (zero ∸ (succ₁ n))
    ≡⟨ cong pred₁ (∸-0S Nn) ⟩
  pred₁ zero
    ≡⟨ pred-0 ⟩
  zero ∎

∸-0x : ∀ {n} → N n → zero ∸ n ≡ zero
∸-0x zN      = ∸-x0 zero
∸-0x (sN Nn) = ∸-0S Nn

∸-SS : ∀ {m n} → N m → N n → succ₁ m ∸ succ₁ n ≡ m ∸ n
∸-SS {m} _ zN =
  rec (succ₁ zero) (succ₁ m) (lam (λ x → lam (λ y → pred₁ y)))
    ≡⟨ rec-S zero (succ₁ m) (lam (λ x → lam (λ y → pred₁ y))) ⟩
  lam (λ x → lam (λ y → pred₁ y))  · zero · (succ₁ m ∸ zero)
    ≡⟨ ·-leftCong (beta (λ x → lam (λ y → pred₁ y)) zero) ⟩
  (λ x → lam (λ y → pred₁ y)) zero · (succ₁ m ∸ zero)
    ≡⟨ refl ⟩
  lam pred₁ · (succ₁ m ∸ zero)
    ≡⟨ beta pred₁ (succ₁ m ∸ zero) ⟩
  pred₁ (succ₁ m ∸ zero)
    ≡⟨ cong pred₁ (∸-x0 (succ₁ m)) ⟩
  pred₁ (succ₁ m)
    ≡⟨ pred-S m ⟩
  m
    ≡⟨ sym (∸-x0 m) ⟩
  m ∸ zero ∎

∸-SS zN (sN {n} Nn) =
  rec (succ₁ (succ₁ n)) (succ₁ zero) (lam (λ x → lam (λ y → pred₁ y)))
    ≡⟨ rec-S (succ₁ n) (succ₁ zero) (lam (λ x → lam (λ y → pred₁ y)))  ⟩
  lam (λ x → lam (λ y → pred₁ y)) · (succ₁ n) · (succ₁ zero ∸ succ₁ n)
    ≡⟨ ·-leftCong (beta (λ x → lam (λ y → pred₁ y)) (succ₁ n)) ⟩
  (λ x → lam (λ y → pred₁ y)) (succ₁ n) · (succ₁ zero ∸ succ₁ n)
    ≡⟨ refl ⟩
  lam pred₁ · (succ₁ zero ∸ succ₁ n)
    ≡⟨ beta pred₁ (succ₁ zero ∸ succ₁ n) ⟩
  pred₁ (succ₁ zero ∸ succ₁ n)
    ≡⟨ cong pred₁ (∸-SS zN Nn) ⟩
  pred₁ (zero ∸ n)
    ≡⟨ cong pred₁ (∸-0x Nn) ⟩
  pred₁ zero
    ≡⟨ pred-0 ⟩
  zero
    ≡⟨ sym (∸-0S Nn) ⟩
  zero ∸ succ₁ n ∎

∸-SS (sN {m} Nm) (sN {n} Nn) =
  rec (succ₁ (succ₁ n)) (succ₁ (succ₁ m)) (lam (λ x → lam (λ y → pred₁ y)))
    ≡⟨ rec-S (succ₁ n) (succ₁ (succ₁ m)) (lam (λ x → lam (λ y → pred₁ y))) ⟩
  lam (λ x → lam (λ y → pred₁ y)) · (succ₁ n) · (succ₁ (succ₁ m) ∸ succ₁ n)
    ≡⟨ ·-leftCong (beta (λ x → lam (λ y → pred₁ y)) (succ₁ n)) ⟩
  (λ x → lam (λ y → pred₁ y)) (succ₁ n) · (succ₁ (succ₁ m) ∸ succ₁ n)
    ≡⟨ refl ⟩
  lam pred₁ · (succ₁ (succ₁ m) ∸ succ₁ n)
    ≡⟨ beta pred₁ (succ₁ (succ₁ m) ∸ succ₁ n) ⟩
  pred₁ (succ₁ (succ₁ m) ∸ succ₁ n)
    ≡⟨ cong pred₁ (∸-SS (sN Nm) Nn) ⟩
  pred₁ (succ₁ m ∸ n)
    ≡⟨ sym (beta pred₁ (succ₁ m ∸ n)) ⟩
  lam pred₁ · (succ₁ m ∸ n)
    ≡⟨ refl ⟩
  (λ x → lam (λ y → pred₁ y)) n · (succ₁ m ∸ n)
    ≡⟨ ·-leftCong (sym (beta (λ x → lam (λ y → pred₁ y)) n)) ⟩
  (lam (λ x → lam (λ y → pred₁ y))) · n · (succ₁ m ∸ n)
    ≡⟨ sym (rec-S n (succ₁ m) (lam (λ x → lam (λ y → pred₁ y)))) ⟩
  rec (succ₁ n) (succ₁ m) (lam (λ x → lam (λ y → pred₁ y)))
    ≡⟨ refl ⟩
  succ₁ m ∸ succ₁ n ∎

*-0x : ∀ n → zero * n ≡ zero
*-0x n = rec zero zero (lam (λ _ → lam (λ y → n + y))) ≡⟨ rec-0 zero ⟩
         zero                                          ∎

*-Sx : ∀ m n → succ₁ m * n ≡ n + m * n
*-Sx m n =
  rec (succ₁ m) zero (lam (λ _ → lam (λ y → n + y)))
    ≡⟨ rec-S m zero (lam (λ _ → lam (λ y → n + y))) ⟩
  (lam (λ _ → lam (λ y → n + y))) · m · (m * n)
    ≡⟨ ·-leftCong (beta (λ _ → lam (λ y → n + y)) m) ⟩
  (λ _ → lam (λ y → n + y)) m · (m * n)
    ≡⟨ refl ⟩
  lam (λ y → n + y) · (m * n)
    ≡⟨ beta (λ y → n + y) (m * n) ⟩
  (λ y → n + y) (m * n)
    ≡⟨ refl ⟩
  n + (m * n) ∎

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N {n = n} zN          Nn = subst N (sym (+-0x n)) Nn
+-N {n = n} (sN {m} Nm) Nn = subst N (sym (+-Sx m n)) (sN (+-N Nm Nn))

∸-N : ∀ {m n} → N m → N n → N (m ∸ n)
∸-N {m} Nm       zN     = subst N (sym (∸-x0 m)) Nm
∸-N     zN      (sN Nn) = subst N (sym (∸-0S Nn)) zN
∸-N     (sN Nm) (sN Nn) = subst N (sym (∸-SS Nm Nn)) (∸-N Nm Nn)

+-leftIdentity : ∀ n → zero + n ≡ n
+-leftIdentity = +-0x

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity zN          = +-leftIdentity zero
+-rightIdentity (sN {n} Nn) =
  trans (+-Sx n zero)
        (subst (λ t → succ₁ (n + zero) ≡ succ₁ t) (+-rightIdentity Nn) refl)


+-assoc : ∀ {m} → N m →  ∀ n o → m + n + o ≡ m + (n + o)
+-assoc zN n o =
  zero + n + o   ≡⟨ subst (λ t → zero + n + o ≡ t + o) (+-leftIdentity n) refl ⟩
  n + o          ≡⟨ sym (+-leftIdentity (n + o)) ⟩
  zero + (n + o) ∎

+-assoc (sN {m} Nm) n o =
  succ₁ m + n + o
    ≡⟨ subst (λ t → succ₁ m + n + o ≡ t + o) (+-Sx m n) refl ⟩
  succ₁ (m + n) + o
    ≡⟨ +-Sx (m + n) o ⟩
  succ₁ (m + n + o)
    ≡⟨ subst (λ t → succ₁ (m + n + o) ≡ succ₁ t) (+-assoc Nm n o) refl ⟩
  succ₁ (m + (n + o))
    ≡⟨ sym (+-Sx m (n + o)) ⟩
  succ₁ m + (n + o) ∎

x+Sy≡S[x+y] : ∀ {m} → N m → ∀ n → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] zN n =
  zero + succ₁ n ≡⟨ +-0x (succ₁ n) ⟩
  succ₁ n ≡⟨ subst (λ t → succ₁ n ≡ succ₁ t) (sym (+-leftIdentity n)) refl ⟩
  succ₁ (zero + n) ∎

x+Sy≡S[x+y] (sN {m} Nm) n =
  succ₁ m + succ₁ n
    ≡⟨ +-Sx m (succ₁ n) ⟩
  succ₁ (m + succ₁ n)
    ≡⟨ subst (λ t → succ₁ (m + succ₁ n) ≡ succ₁ t) (x+Sy≡S[x+y] Nm n) refl ⟩
  succ₁ (succ₁ (m + n))
    ≡⟨ subst (λ t → succ₁ (succ₁ (m + n)) ≡ succ₁ t) (sym (+-Sx m n)) refl ⟩
  succ₁ (succ₁ m + n) ∎

[x+y]∸[x+z]≡y∸z : ∀ {m n o} → N m → N n → N o → (m + n) ∸ (m + o) ≡ n ∸ o
[x+y]∸[x+z]≡y∸z {n = n} {o} zN _ _ =
  (zero + n) ∸ (zero + o)
    ≡⟨ subst (λ t → (zero + n) ∸ (zero + o) ≡ t ∸ (zero + o)) (+-0x n) refl ⟩
    n ∸ (zero + o)
      ≡⟨ subst (λ t → n ∸ (zero + o) ≡ n ∸ t) (+-0x o) refl ⟩
    n ∸ o ∎

[x+y]∸[x+z]≡y∸z {n = n} {o} (sN {m} Nm) Nn No =
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
    ≡⟨ ∸-SS (+-N Nm Nn) (+-N Nm No) ⟩
  (m + n) ∸ (m + o)
    ≡⟨ [x+y]∸[x+z]≡y∸z Nm Nn No ⟩
  n ∸ o ∎

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} zN Nn =
  zero + n ≡⟨ +-leftIdentity n ⟩
  n        ≡⟨ sym (+-rightIdentity Nn) ⟩
  n + zero ∎

+-comm {n = n} (sN {m} Nm) Nn =
  succ₁ m + n   ≡⟨ +-Sx m n ⟩
  succ₁ (m + n) ≡⟨ cong succ₁ (+-comm Nm Nn) ⟩
  succ₁ (n + m) ≡⟨ sym (x+Sy≡S[x+y] Nn m) ⟩
  n + succ₁ m   ∎

*-leftZero : ∀ n → zero * n ≡ zero
*-leftZero = *-0x

*-N : ∀ {m n} → N m → N n → N (m * n)
*-N {n = n} zN          _  = subst N (sym (*-0x n)) zN
*-N {n = n} (sN {m} Nm) Nn = subst N (sym (*-Sx m n)) (+-N Nn (*-N Nm Nn))

*-rightZero : ∀ {n} → N n → n * zero ≡ zero
*-rightZero zN          = *-leftZero zero
*-rightZero (sN {n} Nn) =
  trans (*-Sx n zero)
        (trans (+-leftIdentity (n * zero)) (*-rightZero Nn))

*-leftIdentity : ∀ {n} → N n → succ₁ zero * n ≡ n
*-leftIdentity {n} Nn =
  succ₁ zero * n ≡⟨ *-Sx zero n ⟩
  n + zero * n   ≡⟨ subst (λ t → n + zero * n ≡ n + t) (*-leftZero n) refl ⟩
  n + zero       ≡⟨ +-rightIdentity Nn ⟩
  n              ∎

x*Sy≡x+xy : ∀ {m n} → N m → N n → m * succ₁ n ≡ m + m * n
x*Sy≡x+xy {n = n} zN _ = sym
  ( zero + zero * n
      ≡⟨ subst (λ t → zero + zero * n ≡ zero + t) (*-leftZero n) refl ⟩
    zero + zero
      ≡⟨ +-leftIdentity zero ⟩
    zero
      ≡⟨ sym (*-leftZero (succ₁ n)) ⟩
    zero * succ₁ n ∎
  )

x*Sy≡x+xy {n = n} (sN {m} Nm) Nn =
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
             (sym (+-assoc Nn m (m * n)))
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
    ≡⟨ sym (+-Sx m (n + m * n)) ⟩
  succ₁ m + (n + m * n)
    ≡⟨ subst (λ t → succ₁ m + (n + m * n) ≡ succ₁ m + t)
             (sym (*-Sx m n))
             refl
    ⟩
  succ₁ m + succ₁ m * n ∎

*-comm : ∀ {m n} → N m → N n → m * n ≡ n * m
*-comm {n = n} zN Nn          = trans (*-leftZero n) (sym (*-rightZero Nn))
*-comm {n = n} (sN {m} Nm) Nn =
  succ₁ m * n  ≡⟨ *-Sx m n ⟩
  n + m * n    ≡⟨ subst (λ t → n + m * n ≡ n + t) (*-comm Nm Nn) refl ⟩
  n + n * m    ≡⟨ sym (x*Sy≡x+xy Nn Nm) ⟩
  n * succ₁ m  ∎

*∸-leftDistributive : ∀ {m n o} → N m → N n → N o → (m ∸ n) * o ≡ m * o ∸ n * o
*∸-leftDistributive {m} {o = o} _ zN _ =
  (m ∸ zero) * o   ≡⟨ subst (λ t → (m ∸ zero) * o ≡ t * o) (∸-x0 m) refl ⟩
  m * o            ≡⟨ sym (∸-x0 (m * o)) ⟩
  m * o ∸ zero     ≡⟨ subst (λ t → m * o ∸ zero ≡ m * o ∸ t) (sym (*-0x o)) refl ⟩
  m * o ∸ zero * o ∎

*∸-leftDistributive {o = o} zN (sN {n} Nn) No =
  (zero ∸ succ₁ n) * o
    ≡⟨ subst (λ t → (zero ∸ succ₁ n) * o ≡ t * o) (∸-0S Nn) refl ⟩
  zero * o
    ≡⟨ *-0x o ⟩
  zero
    ≡⟨ sym (∸-0x (*-N (sN Nn) No)) ⟩
  zero ∸ succ₁ n * o
    ≡⟨ subst (λ t → zero ∸ succ₁ n * o ≡ t ∸ succ₁ n * o)
             (sym (*-0x o))
             refl
    ⟩
  zero * o ∸ succ₁ n * o ∎

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) zN =
  (succ₁ m ∸ succ₁ n) * zero
    ≡⟨ *-comm (∸-N (sN Nm) (sN Nn)) zN ⟩
  zero * (succ₁ m ∸ succ₁ n)
    ≡⟨ *-0x (succ₁ m ∸ succ₁ n) ⟩
  zero
    ≡⟨ sym (∸-0x (*-N (sN Nn) zN)) ⟩
  zero ∸ succ₁ n * zero
    ≡⟨ subst (λ t → zero ∸ succ₁ n * zero ≡ t ∸ succ₁ n * zero)
             (sym (*-0x (succ₁ m)))
             refl
    ⟩
  zero * succ₁ m ∸ succ₁ n * zero
    ≡⟨ subst (λ t → zero * succ₁ m ∸ succ₁ n * zero ≡ t ∸ succ₁ n * zero)
             (*-comm zN (sN Nm))
             refl
    ⟩
  succ₁ m * zero ∸ succ₁ n * zero ∎

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  (succ₁ m ∸ succ₁ n) * succ₁ o
    ≡⟨ subst (λ t → (succ₁ m ∸ succ₁ n) * succ₁ o ≡ t * succ₁ o)
             (∸-SS Nm Nn)
             refl
    ⟩
  (m ∸ n) * succ₁ o
    ≡⟨ *∸-leftDistributive Nm Nn (sN No) ⟩
  m * succ₁ o ∸ n * succ₁ o
    ≡⟨ sym ([x+y]∸[x+z]≡y∸z (sN No) (*-N Nm (sN No)) (*-N Nn (sN No))) ⟩
  (succ₁ o + m * succ₁ o) ∸ (succ₁ o + n * succ₁ o)
    ≡⟨ subst (λ t → (succ₁ o + m * succ₁ o) ∸ (succ₁ o + n * succ₁ o) ≡
                    t ∸ (succ₁ o + n * succ₁ o))
             (sym (*-Sx m (succ₁ o)))
             refl
    ⟩
  (succ₁ m * succ₁ o) ∸ (succ₁ o + n * succ₁ o)
    ≡⟨ subst (λ t → (succ₁ m * succ₁ o) ∸ (succ₁ o + n * succ₁ o) ≡
                    (succ₁ m * succ₁ o) ∸ t)
             (sym (*-Sx n (succ₁ o)))
             refl
    ⟩
  (succ₁ m * succ₁ o) ∸ (succ₁ n * succ₁ o) ∎

*+-leftDistributive : ∀ {m n o} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
*+-leftDistributive {m} {n} Nm Nn zN =
  (m + n) * zero       ≡⟨ *-comm (+-N Nm Nn) zN ⟩
  zero * (m + n)       ≡⟨ *-0x (m + n) ⟩
  zero                 ≡⟨ sym (*-0x m) ⟩
  zero * m             ≡⟨ *-comm zN Nm ⟩
  m * zero             ≡⟨ sym (+-rightIdentity (*-N Nm zN)) ⟩
  m * zero + zero      ≡⟨ subst (λ t → m * zero + zero ≡ m * zero + t)
                                (trans (sym (*-0x n)) (*-comm zN Nn))
                                  refl
                       ⟩
  m * zero + n * zero  ∎

*+-leftDistributive {n = n} zN Nn (sN {o} No) =
  (zero + n) * succ₁ o
    ≡⟨ subst (λ t → (zero + n) * succ₁ o ≡ t * succ₁ o)
             (+-leftIdentity n)
             refl
    ⟩
  n * succ₁ o
    ≡⟨ sym (+-leftIdentity (n * succ₁ o)) ⟩
  zero + n * succ₁ o
    ≡⟨ subst (λ t → zero + n * succ₁ o ≡ t +  n * succ₁ o)
             (sym (*-0x (succ₁ o)))
             refl
    ⟩
  zero * succ₁ o + n * succ₁ o ∎

*+-leftDistributive (sN {m} Nm) zN (sN {o} No) =
  (succ₁ m + zero) * succ₁ o
    ≡⟨ subst (λ t → (succ₁ m + zero) * succ₁ o ≡ t * succ₁ o)
             (+-rightIdentity (sN Nm))
             refl
    ⟩
  succ₁ m * succ₁ o
    ≡⟨ sym (+-rightIdentity (*-N (sN Nm) (sN No))) ⟩
  succ₁ m * succ₁ o + zero
    ≡⟨ subst (λ t → succ₁ m * succ₁ o + zero ≡ succ₁ m * succ₁ o + t)
             (sym (*-leftZero (succ₁ o)))
             refl
    ⟩
    succ₁ m * succ₁ o + zero * succ₁ o ∎

*+-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  (succ₁ m + succ₁ n) * succ₁ o
    ≡⟨ subst (λ t → (succ₁ m + succ₁ n) * succ₁ o ≡ t * succ₁ o)
             (+-Sx m (succ₁ n))
             refl
    ⟩
  succ₁ (m + succ₁ n) * succ₁ o
    ≡⟨ *-Sx (m + succ₁ n) (succ₁ o) ⟩
  succ₁ o + (m + succ₁ n) * succ₁ o
    ≡⟨ subst (λ t → succ₁ o + (m + succ₁ n) * succ₁ o ≡ succ₁ o + t)
             (*+-leftDistributive Nm (sN Nn) (sN No))
             refl
    ⟩
  succ₁ o + (m * succ₁ o + succ₁ n * succ₁ o)
    ≡⟨ sym (+-assoc (sN No) (m * succ₁ o) (succ₁ n * succ₁ o)) ⟩
  succ₁ o + m * succ₁ o + succ₁ n * succ₁ o
    ≡⟨ subst (λ t → succ₁ o + m * succ₁ o + succ₁ n * succ₁ o ≡
                    t + succ₁ n * succ₁ o)
             (sym (*-Sx m (succ₁ o)))
             refl
    ⟩
  succ₁ m * succ₁ o + succ₁ n * succ₁ o ∎
