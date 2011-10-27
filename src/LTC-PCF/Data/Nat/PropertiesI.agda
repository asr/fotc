------------------------------------------------------------------------------
-- Arithmetic properties
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.PropertiesI where

open import LTC-PCF.Base

open import Common.Function using ( _$_ )

open import LTC-PCF.Data.Nat
  using ( _+_ ; +-helper
        ; _∸_ ; ∸-helper
        ; _*_ ; *-helper₁ ; *-helper₂
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Rec using ( rec )
open import LTC-PCF.Data.Nat.Rec.EquationsI using ( rec-0 ; rec-S )

open import LTC-PCF.Relation.Binary.EqReasoning

------------------------------------------------------------------------------

+-0x : ∀ d → zero + d ≡ d
+-0x d =
  begin
    rec zero d (lam +-helper) ≡⟨ rec-0 d ⟩
    d
  ∎

+-Sx : ∀ d e → succ₁ d + e ≡ succ₁ (d + e)
+-Sx d e =
  begin
    rec (succ₁ d) e (lam +-helper) ≡⟨ rec-S d e (lam +-helper) ⟩
    lam +-helper · d · (d + e)
      ≡⟨ subst (λ t → lam +-helper · d · (d + e) ≡ t · (d + e))
               (beta +-helper d)
               refl
      ⟩
    +-helper d · (d + e) ≡⟨ refl ⟩
    lam succ₁ · (d + e) ≡⟨ beta succ₁ (d + e) ⟩
    succ₁ (d + e)
  ∎

∸-x0 : ∀ d → d ∸ zero ≡ d
∸-x0 d =
  begin
    rec zero d (lam ∸-helper) ≡⟨ rec-0 d ⟩
    d
  ∎

∸-0S : ∀ {n} → N n → zero ∸ succ₁ n ≡ zero
∸-0S zN =
  begin
    rec (succ₁ zero) zero (lam ∸-helper) ≡⟨ rec-S zero zero (lam ∸-helper) ⟩
    lam ∸-helper · zero · (zero ∸ zero)
      ≡⟨ subst (λ t → lam ∸-helper · zero · (zero ∸ zero) ≡
                      t · (zero ∸ zero))
               (beta ∸-helper zero)
               refl
      ⟩
    ∸-helper zero · (zero ∸ zero) ≡⟨ refl ⟩
    lam pred₁ · (zero ∸ zero) ≡⟨ beta pred₁ (zero ∸ zero) ⟩
    pred₁ (zero ∸ zero)
      ≡⟨ subst (λ t → pred₁ (zero ∸ zero) ≡ pred₁ t) (∸-x0 zero) refl ⟩
    pred₁ zero ≡⟨ pred-0 ⟩
    zero
  ∎

∸-0S (sN {n} Nn) =
  begin
    rec (succ₁ (succ₁ n)) zero (lam ∸-helper)
      ≡⟨ rec-S (succ₁ n) zero (lam ∸-helper) ⟩
    lam ∸-helper · (succ₁ n) · (zero ∸ (succ₁ n))
      ≡⟨ subst (λ t → lam ∸-helper · (succ₁ n) · (zero ∸ (succ₁ n)) ≡
                      t · (zero ∸ (succ₁ n)))
               (beta ∸-helper (succ₁ n))
               refl
      ⟩
    ∸-helper (succ₁ n) · (zero ∸ (succ₁ n)) ≡⟨ refl ⟩
    lam pred₁ · (zero ∸ (succ₁ n))
      ≡⟨ beta pred₁ (zero ∸ (succ₁ n)) ⟩
    pred₁ (zero ∸ (succ₁ n))
      ≡⟨ subst (λ t → pred₁ (zero ∸ (succ₁ n)) ≡ pred₁ t) (∸-0S Nn) refl ⟩
    pred₁ zero ≡⟨ pred-0 ⟩
    zero
  ∎

∸-0x : ∀ {n} → N n → zero ∸ n ≡ zero
∸-0x zN      = ∸-x0 zero
∸-0x (sN Nn) = ∸-0S Nn

∸-SS : ∀ {m n} → N m → N n → succ₁ m ∸ succ₁ n ≡ m ∸ n
∸-SS {m} _ zN =
  begin
    rec (succ₁ zero) (succ₁ m) (lam ∸-helper)
      ≡⟨ rec-S zero (succ₁ m) (lam ∸-helper) ⟩
    lam ∸-helper · zero · (succ₁ m ∸ zero)
      ≡⟨ subst (λ t → lam ∸-helper · zero · (succ₁ m ∸ zero) ≡
                      t · (succ₁ m ∸ zero))
               (beta ∸-helper zero)
               refl
      ⟩
    ∸-helper zero · (succ₁ m ∸ zero) ≡⟨ refl ⟩
    lam pred₁ · (succ₁ m ∸ zero) ≡⟨ beta pred₁ (succ₁ m ∸ zero) ⟩
    pred₁ (succ₁ m ∸ zero)
      ≡⟨ subst (λ t → pred₁ (succ₁ m ∸ zero) ≡ pred₁ t) (∸-x0 (succ₁ m)) refl ⟩
    pred₁ (succ₁ m) ≡⟨ pred-S m ⟩
    m ≡⟨ sym $ ∸-x0 m ⟩
    m ∸ zero
  ∎

∸-SS zN (sN {n} Nn) =
  begin
    rec (succ₁ (succ₁ n)) (succ₁ zero) (lam ∸-helper)
      ≡⟨ rec-S (succ₁ n) (succ₁ zero) (lam ∸-helper) ⟩
    lam ∸-helper · (succ₁ n) · (succ₁ zero ∸ succ₁ n)
      ≡⟨ subst (λ t → lam ∸-helper · (succ₁ n) · (succ₁ zero ∸ succ₁ n) ≡
                      t · (succ₁ zero ∸ succ₁ n))
               (beta ∸-helper (succ₁ n))
               refl
      ⟩
    ∸-helper (succ₁ n) · (succ₁ zero ∸ succ₁ n) ≡⟨ refl ⟩
    lam pred₁ · (succ₁ zero ∸ succ₁ n)
      ≡⟨ beta pred₁ (succ₁ zero ∸ succ₁ n) ⟩
    pred₁ (succ₁ zero ∸ succ₁ n)
      ≡⟨ subst (λ t → pred₁ (succ₁ zero ∸ succ₁ n) ≡ pred₁ t) (∸-SS zN Nn) refl ⟩
    pred₁ (zero ∸ n) ≡⟨ subst (λ t → pred₁ (zero ∸ n) ≡ pred₁ t) (∸-0x Nn) refl ⟩
    pred₁ zero       ≡⟨ pred-0 ⟩
    zero            ≡⟨ sym $ ∸-0S Nn ⟩
    zero ∸ succ₁ n
  ∎

∸-SS (sN {m} Nm) (sN {n} Nn) =
  begin
    rec (succ₁ (succ₁ n)) (succ₁ (succ₁ m)) (lam ∸-helper)
      ≡⟨ rec-S (succ₁ n) (succ₁ (succ₁ m)) (lam ∸-helper) ⟩
    lam ∸-helper · (succ₁ n) · (succ₁ (succ₁ m) ∸ succ₁ n)
      ≡⟨ subst (λ t → lam ∸-helper · (succ₁ n) · (succ₁ (succ₁ m) ∸ succ₁ n) ≡
                      t · (succ₁ (succ₁ m) ∸ succ₁ n))
               (beta ∸-helper (succ₁ n))
               refl
      ⟩
    ∸-helper (succ₁ n) · (succ₁ (succ₁ m) ∸ succ₁ n) ≡⟨ refl ⟩
    lam pred₁ · (succ₁ (succ₁ m) ∸ succ₁ n)
      ≡⟨ beta pred₁ (succ₁ (succ₁ m) ∸ succ₁ n) ⟩
    pred₁ (succ₁ (succ₁ m) ∸ succ₁ n)
      ≡⟨ subst (λ t → pred₁ (succ₁ (succ₁ m) ∸ succ₁ n) ≡ pred₁ t)
               (∸-SS (sN Nm) Nn)
               refl
      ⟩
    pred₁ (succ₁ m ∸ n) ≡⟨ sym $ beta pred₁ (succ₁ m ∸ n) ⟩
    lam pred₁ · (succ₁ m ∸ n) ≡⟨ refl ⟩
    ∸-helper n · (succ₁ m ∸ n)
      ≡⟨ subst (λ t → ∸-helper n · (succ₁ m ∸ n) ≡ t · (succ₁ m ∸ n))
               (sym $ beta ∸-helper n)
               refl
      ⟩
    (lam ∸-helper) · n · (succ₁ m ∸ n)
      ≡⟨ sym $ rec-S n (succ₁ m) (lam ∸-helper) ⟩
    rec (succ₁ n) (succ₁ m) (lam ∸-helper) ≡⟨ refl ⟩
    succ₁ m ∸ succ₁ n
  ∎

*-0x : ∀ d → zero * d ≡ zero
*-0x d =
  begin
    rec zero zero (lam (*-helper₂ d)) ≡⟨ rec-0 zero ⟩
    zero
  ∎

*-Sx : ∀ d e → succ₁ d * e ≡ e + d * e
*-Sx d e =
  begin
    rec (succ₁ d) zero (lam (*-helper₂ e)) ≡⟨ rec-S d zero (lam (*-helper₂ e)) ⟩
    lam (*-helper₂ e) · d · (d * e)
      ≡⟨ subst (λ t → lam (*-helper₂ e) · d · (d * e) ≡ t · (d * e))
               (beta (*-helper₂ e) d)
               refl
      ⟩
    *-helper₂ e d · (d * e)     ≡⟨ refl ⟩
    lam (*-helper₁ e) · (d * e) ≡⟨ beta (*-helper₁ e) (d * e) ⟩
    *-helper₁ e (d * e)         ≡⟨ refl ⟩
    e + (d * e)
  ∎

∸-N : ∀ {m n} → N m → N n → N (m ∸ n)
∸-N {m} Nm       zN     = subst N (sym $ ∸-x0 m) Nm
∸-N     zN      (sN Nn) = subst N (sym $ ∸-0S Nn) zN
∸-N     (sN Nm) (sN Nn) = subst N (sym $ ∸-SS Nm Nn) (∸-N Nm Nn)

+-leftIdentity : ∀ {n} → N n → zero + n ≡ n
+-leftIdentity {n} _ = +-0x n

+-rightIdentity : ∀ {n} → N n → n + zero ≡ n
+-rightIdentity zN          = +-leftIdentity zN
+-rightIdentity (sN {n} Nn) =
  trans (+-Sx n zero)
        (subst (λ t → succ₁ (n + zero) ≡ succ₁ t) (+-rightIdentity Nn) refl)

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N zN       Nn            = subst N (sym $ +-leftIdentity Nn) Nn
+-N {n = n} (sN {m} Nm) Nn = subst N (sym $ +-Sx m n) (sN (+-N Nm Nn))

+-assoc : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} zN Nn No =
  begin
    zero + n + o ≡⟨ subst (λ t → zero + n + o ≡ t + o) (+-leftIdentity Nn) refl ⟩
    n + o        ≡⟨ sym $ +-leftIdentity (+-N Nn No) ⟩
    zero + (n + o)
  ∎

+-assoc {n = n} {o} (sN {m} Nm) Nn No =
  begin
    succ₁ m + n + o
      ≡⟨ subst (λ t → succ₁ m + n + o ≡ t + o) (+-Sx m n) refl ⟩
    succ₁ (m + n) + o
      ≡⟨ +-Sx (m + n) o ⟩
    succ₁ (m + n + o)
      ≡⟨ subst (λ t → succ₁ (m + n + o) ≡ succ₁ t) (+-assoc Nm Nn No) refl ⟩
    succ₁ (m + (n + o))
      ≡⟨ sym $ +-Sx m (n + o) ⟩
    succ₁ m + (n + o)
  ∎

x+Sy≡S[x+y] : ∀ {m n} → N m → N n → m + succ₁ n ≡ succ₁ (m + n)
x+Sy≡S[x+y] {n = n} zN Nn =
  begin
    zero + succ₁ n ≡⟨ +-0x (succ₁ n) ⟩
    succ₁ n ≡⟨ subst (λ t → succ₁ n ≡ succ₁ t) (sym $ +-leftIdentity Nn) refl ⟩
    succ₁ (zero + n)
  ∎

x+Sy≡S[x+y] {n = n} (sN {m} Nm) Nn =
  begin
    succ₁ m + succ₁ n
      ≡⟨ +-Sx m (succ₁ n) ⟩
    succ₁ (m + succ₁ n)
      ≡⟨ subst (λ t → succ₁ (m + succ₁ n) ≡ succ₁ t) (x+Sy≡S[x+y] Nm Nn) refl ⟩
    succ₁ (succ₁ (m + n))
      ≡⟨ subst (λ t → succ₁ (succ₁ (m + n)) ≡ succ₁ t) (sym $ +-Sx m n) refl ⟩
    succ₁ (succ₁ m + n)
  ∎

[x+y]∸[x+z]≡y∸z : ∀ {m n o} → N m → N n → N o → (m + n) ∸ (m + o) ≡ n ∸ o
[x+y]∸[x+z]≡y∸z {n = n} {o} zN _ _ =
  begin
    (zero + n) ∸ (zero + o)
      ≡⟨ subst (λ t → (zero + n) ∸ (zero + o) ≡ t ∸ (zero + o)) (+-0x n) refl ⟩
     n ∸ (zero + o)
       ≡⟨ subst (λ t → n ∸ (zero + o) ≡ n ∸ t) (+-0x o) refl ⟩
     n ∸ o
  ∎

[x+y]∸[x+z]≡y∸z {n = n} {o} (sN {m} Nm) Nn No =
  begin
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
    succ₁ (m + n) ∸ succ₁ (m + o) ≡⟨ ∸-SS (+-N Nm Nn) (+-N Nm No) ⟩
    (m + n) ∸ (m + o) ≡⟨ [x+y]∸[x+z]≡y∸z Nm Nn No ⟩
    n ∸ o
  ∎

+-comm : ∀ {m n} → N m → N n → m + n ≡ n + m
+-comm {n = n} zN Nn =
  begin
    zero + n ≡⟨ +-leftIdentity Nn ⟩
    n        ≡⟨ sym $ +-rightIdentity Nn ⟩
    n + zero
   ∎

+-comm {n = n} (sN {m} Nm) Nn =
  begin
    succ₁ m + n   ≡⟨ +-Sx m n ⟩
    succ₁ (m + n) ≡⟨ subst (λ t → succ₁ (m + n) ≡ succ₁ t) (+-comm Nm Nn) refl ⟩
    succ₁ (n + m) ≡⟨ sym $ x+Sy≡S[x+y] Nn Nm ⟩
    n + succ₁ m
   ∎

*-leftZero : ∀ n → zero * n ≡ zero
*-leftZero = *-0x

*-N : ∀ {m n} → N m → N n → N (m * n)
*-N {n = n} zN          _  = subst N (sym $ *-leftZero n) zN
*-N {n = n} (sN {m} Nm) Nn = subst N (sym $ *-Sx m n) (+-N Nn (*-N Nm Nn))

*-rightZero : ∀ {n} → N n → n * zero ≡ zero
*-rightZero zN          = *-leftZero zero
*-rightZero (sN {n} Nn) =
  trans (*-Sx n zero)
        (trans (+-leftIdentity (*-N Nn zN)) (*-rightZero Nn))

*-leftIdentity : ∀ {n} → N n → succ₁ zero * n ≡ n
*-leftIdentity {n} Nn =
  begin
    succ₁ zero * n ≡⟨ *-Sx zero n ⟩
    n + zero * n   ≡⟨ subst (λ t → n + zero * n ≡ n + t) (*-leftZero n) refl ⟩
      n + zero     ≡⟨ +-rightIdentity Nn ⟩
    n
  ∎

x*Sy≡x+xy : ∀ {m n} → N m → N n → m * succ₁ n ≡ m + m * n
x*Sy≡x+xy {n = n} zN _ = sym
  (
    begin
      zero + zero * n
        ≡⟨ subst (λ t → zero + zero * n ≡ zero + t) (*-leftZero n) refl ⟩
      zero + zero
        ≡⟨ +-leftIdentity zN ⟩
      zero
        ≡⟨ sym $ *-leftZero (succ₁ n) ⟩
      zero * succ₁ n
    ∎
  )

x*Sy≡x+xy {n = n} (sN {m} Nm) Nn =
  begin
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
               (sym $ +-assoc Nn Nm (*-N Nm Nn))
               refl
      ⟩
    succ₁ (n + m + m * n)
      ≡⟨ subst (λ t → succ₁ (n + m + m * n) ≡ succ₁ (t + m * n))
               (+-comm Nn Nm)
               refl
      ⟩
     succ₁ (m + n + m * n)
     ≡⟨ subst (λ t → succ₁ (m + n + m * n) ≡ succ₁ t)
              (+-assoc Nm Nn (*-N Nm Nn))
              refl
     ⟩
    succ₁ (m + (n + m * n))
      ≡⟨ sym $ +-Sx m (n + m * n) ⟩
    succ₁ m + (n + m * n)
      ≡⟨ subst (λ t → succ₁ m + (n + m * n) ≡ succ₁ m + t)
               (sym $ *-Sx m n)
               refl
      ⟩
    succ₁ m + succ₁ m * n
    ∎

*-comm : ∀ {m n} → N m → N n → m * n ≡ n * m
*-comm {n = n} zN Nn          = trans (*-leftZero n) (sym $ *-rightZero Nn)
*-comm {n = n} (sN {m} Nm) Nn =
  begin
    succ₁ m * n   ≡⟨ *-Sx m n ⟩
    n + m * n     ≡⟨ subst (λ t → n + m * n ≡ n + t) (*-comm Nm Nn) refl ⟩
    n + n * m     ≡⟨ sym $ x*Sy≡x+xy Nn Nm ⟩
    n * succ₁ m
  ∎

*∸-leftDistributive : ∀ {m n o} → N m → N n → N o → (m ∸ n) * o ≡ m * o ∸ n * o
*∸-leftDistributive {m} {o = o} _ zN _ =
  begin
    (m ∸ zero) * o ≡⟨ subst (λ t → (m ∸ zero) * o ≡ t * o) (∸-x0 m) refl ⟩
    m * o ≡⟨ sym $ ∸-x0 (m * o) ⟩
    m * o ∸ zero ≡⟨ subst (λ t → m * o ∸ zero ≡ m * o ∸ t) (sym $ *-0x o) refl ⟩
    m * o ∸ zero * o
  ∎

*∸-leftDistributive {o = o} zN (sN {n} Nn) No =
  begin
    (zero ∸ succ₁ n) * o
      ≡⟨ subst (λ t → (zero ∸ succ₁ n) * o ≡ t * o) (∸-0S Nn) refl ⟩
    zero * o
      ≡⟨ *-0x o ⟩
    zero
      ≡⟨ sym $ ∸-0x (*-N (sN Nn) No) ⟩
    zero ∸ succ₁ n * o
      ≡⟨ subst (λ t → zero ∸ succ₁ n * o ≡ t ∸ succ₁ n * o)
               (sym $ *-0x o)
               refl
      ⟩
    zero * o ∸ succ₁ n * o
  ∎

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) zN =
  begin
    (succ₁ m ∸ succ₁ n) * zero ≡⟨ *-comm (∸-N (sN Nm) (sN Nn)) zN ⟩
    zero * (succ₁ m ∸ succ₁ n) ≡⟨ *-0x (succ₁ m ∸ succ₁ n) ⟩
    zero ≡⟨ sym $ ∸-0x (*-N (sN Nn) zN) ⟩
    zero ∸ succ₁ n * zero
      ≡⟨ subst (λ t → zero ∸ succ₁ n * zero ≡ t ∸ succ₁ n * zero)
               (sym $ *-0x (succ₁ m))
               refl
      ⟩
    zero * succ₁ m ∸ succ₁ n * zero
      ≡⟨ subst (λ t → zero * succ₁ m ∸ succ₁ n * zero ≡ t ∸ succ₁ n * zero)
               (*-comm zN (sN Nm))
               refl
      ⟩
    succ₁ m * zero ∸ succ₁ n * zero
  ∎

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  begin
    (succ₁ m ∸ succ₁ n) * succ₁ o
      ≡⟨ subst (λ t → (succ₁ m ∸ succ₁ n) * succ₁ o ≡ t * succ₁ o)
               (∸-SS Nm Nn)
               refl
      ⟩
    (m ∸ n) * succ₁ o ≡⟨ *∸-leftDistributive Nm Nn (sN No) ⟩
    m * succ₁ o ∸ n * succ₁ o
      ≡⟨ sym $ [x+y]∸[x+z]≡y∸z (sN No) (*-N Nm (sN No)) (*-N Nn (sN No)) ⟩
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
    (succ₁ m * succ₁ o) ∸ (succ₁ n * succ₁ o)
  ∎

*+-leftDistributive : ∀ {m n o} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
*+-leftDistributive {m} {n} Nm Nn zN =
  begin
    (m + n) * zero       ≡⟨ *-comm (+-N Nm Nn) zN ⟩
    zero * (m + n)       ≡⟨ *-0x (m + n) ⟩
    zero                 ≡⟨ sym $ *-0x m ⟩
    zero * m             ≡⟨ *-comm zN Nm ⟩
    m * zero             ≡⟨ sym $ +-rightIdentity (*-N Nm zN) ⟩
    m * zero + zero      ≡⟨ subst (λ t → m * zero + zero ≡ m * zero + t)
                                  (trans (sym $ *-0x n) (*-comm zN Nn))
                                  refl
                         ⟩
    m * zero + n * zero
  ∎

*+-leftDistributive {n = n} zN Nn (sN {o} No) =
  begin
    (zero + n) * succ₁ o  ≡⟨ subst (λ t → (zero + n) * succ₁ o ≡ t * succ₁ o)
                                   (+-leftIdentity Nn)
                                   refl
                          ⟩
    n * succ₁ o           ≡⟨ sym $ +-leftIdentity (*-N Nn (sN No)) ⟩
    zero + n * succ₁ o    ≡⟨ subst (λ t → zero + n * succ₁ o ≡ t +  n * succ₁ o)
                                   (sym $ *-0x (succ₁ o))
                                   refl
                          ⟩
    zero * succ₁ o + n * succ₁ o
  ∎

*+-leftDistributive (sN {m} Nm) zN (sN {o} No) =
 begin
    (succ₁ m + zero) * succ₁ o
      ≡⟨ subst (λ t → (succ₁ m + zero) * succ₁ o ≡ t * succ₁ o)
               (+-rightIdentity (sN Nm))
               refl
      ⟩
    succ₁ m * succ₁ o ≡⟨ sym $ +-rightIdentity (*-N (sN Nm) (sN No)) ⟩
    succ₁ m * succ₁ o + zero
      ≡⟨ subst (λ t → succ₁ m * succ₁ o + zero ≡ succ₁ m * succ₁ o + t)
               (sym $ *-leftZero (succ₁ o))
               refl
      ⟩
    succ₁ m * succ₁ o + zero * succ₁ o
  ∎

*+-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  begin
    (succ₁ m + succ₁ n) * succ₁ o
      ≡⟨ subst (λ t → (succ₁ m + succ₁ n) * succ₁ o ≡ t * succ₁ o)
               (+-Sx m (succ₁ n))
               refl
      ⟩
    succ₁ (m + succ₁ n) * succ₁ o ≡⟨ *-Sx (m + succ₁ n) (succ₁ o) ⟩
    succ₁ o + (m + succ₁ n) * succ₁ o
      ≡⟨ subst (λ t → succ₁ o + (m + succ₁ n) * succ₁ o ≡ succ₁ o + t)
               (*+-leftDistributive Nm (sN Nn) (sN No))
               refl
      ⟩
    succ₁ o + (m * succ₁ o + succ₁ n * succ₁ o)
      ≡⟨ sym $ +-assoc (sN No) (*-N Nm (sN No)) (*-N (sN Nn) (sN No)) ⟩
    succ₁ o + m * succ₁ o + succ₁ n * succ₁ o
      ≡⟨ subst (λ t → succ₁ o + m * succ₁ o + succ₁ n * succ₁ o ≡
                      t + succ₁ n * succ₁ o)
               (sym $ *-Sx m (succ₁ o))
               refl
      ⟩
    succ₁ m * succ₁ o + succ₁ n * succ₁ o
      ∎
