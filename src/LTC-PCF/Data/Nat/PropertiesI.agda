------------------------------------------------------------------------------
-- Arithmetic properties
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.PropertiesI where

open import LTC.Base

open import Common.Function using ( _$_ )

open import LTC.Relation.Binary.EqReasoning

open import LTC-PCF.Data.Nat
  using ( _+_ ; +-helper
        ; _∸_ ; ∸-helper
        ; _*_ ; *-helper₁ ; *-helper₂
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Rec using ( rec )
open import LTC-PCF.Data.Nat.Rec.EquationsI using ( rec-0 ; rec-S )

------------------------------------------------------------------------------

+-0x : ∀ d → zero + d ≡ d
+-0x d =
  begin
    rec zero d (lam +-helper) ≡⟨ rec-0 d ⟩
    d
  ∎

+-Sx : ∀ d e → succ d + e ≡ succ (d + e)
+-Sx d e =
  begin
    rec (succ d) e (lam +-helper) ≡⟨ rec-S d e (lam +-helper) ⟩
    lam +-helper · d · (d + e)    ≡⟨ subst (λ t → lam +-helper · d · (d + e) ≡
                                               t · (d + e))
                                         (beta +-helper d)
                                         refl
                                  ⟩
    +-helper d · (d + e)          ≡⟨ refl ⟩
    lam succ · (d + e)            ≡⟨ beta succ (d + e) ⟩
    succ (d + e)
  ∎

∸-x0 : ∀ d → d ∸ zero ≡ d
∸-x0 d =
  begin
    rec zero d (lam ∸-helper) ≡⟨ rec-0 d ⟩
    d
  ∎

∸-0S : ∀ {n} → N n → zero ∸ succ n ≡ zero
∸-0S zN =
  begin
    rec (succ zero) zero (lam ∸-helper) ≡⟨ rec-S zero zero (lam ∸-helper) ⟩
    lam ∸-helper · zero · (zero ∸ zero)
      ≡⟨ subst (λ t → lam ∸-helper · zero · (zero ∸ zero) ≡
                      t · (zero ∸ zero))
               (beta ∸-helper zero)
               refl
      ⟩
    ∸-helper zero · (zero ∸ zero) ≡⟨ refl ⟩
    lam pred · (zero ∸ zero)      ≡⟨ beta pred (zero ∸ zero) ⟩
    pred (zero ∸ zero)            ≡⟨ subst (λ t → pred (zero ∸ zero) ≡ pred t)
                                           (∸-x0 zero)
                                           refl
                                  ⟩
    pred zero                     ≡⟨ pred-0 ⟩
    zero
  ∎

∸-0S (sN {n} Nn) =
  begin
    rec (succ (succ n)) zero (lam ∸-helper)
      ≡⟨ rec-S (succ n) zero (lam ∸-helper) ⟩
    lam ∸-helper · (succ n) · (zero ∸ (succ n))
      ≡⟨ subst (λ t → lam ∸-helper · (succ n) · (zero ∸ (succ n)) ≡
                      t · (zero ∸ (succ n)))
               (beta ∸-helper (succ n))
               refl
      ⟩
    ∸-helper (succ n) · (zero ∸ (succ n)) ≡⟨ refl ⟩
    lam pred · (zero ∸ (succ n))
      ≡⟨ beta pred (zero ∸ (succ n)) ⟩
    pred (zero ∸ (succ n)) ≡⟨ subst (λ t → pred (zero ∸ (succ n)) ≡ pred t)
                                    (∸-0S Nn)
                                    refl
                           ⟩
    pred zero              ≡⟨ pred-0 ⟩
    zero
  ∎

∸-0x : ∀ {n} → N n → zero ∸ n ≡ zero
∸-0x zN      = ∸-x0 zero
∸-0x (sN Nn) = ∸-0S Nn

∸-SS : ∀ {m n} → N m → N n → succ m ∸ succ n ≡ m ∸ n
∸-SS {m} _ zN =
  begin
    rec (succ zero) (succ m) (lam ∸-helper)
      ≡⟨ rec-S zero (succ m) (lam ∸-helper) ⟩
    lam ∸-helper · zero · (succ m ∸ zero)
      ≡⟨ subst (λ t → lam ∸-helper · zero · (succ m ∸ zero) ≡
                      t · (succ m ∸ zero))
               (beta ∸-helper zero)
               refl
      ⟩
    ∸-helper zero · (succ m ∸ zero) ≡⟨ refl ⟩
    lam pred · (succ m ∸ zero)      ≡⟨ beta pred (succ m ∸ zero) ⟩
    pred (succ m ∸ zero)
      ≡⟨ subst (λ t → pred (succ m ∸ zero) ≡ pred t)
               (∸-x0 (succ m))
               refl
      ⟩
    pred (succ m) ≡⟨ pred-S m ⟩
    m             ≡⟨ sym $ ∸-x0 m ⟩
    m ∸ zero
  ∎

∸-SS zN (sN {n} Nn) =
  begin
    rec (succ (succ n)) (succ zero) (lam ∸-helper)
      ≡⟨ rec-S (succ n) (succ zero) (lam ∸-helper) ⟩
    lam ∸-helper · (succ n) · (succ zero ∸ succ n)
      ≡⟨ subst (λ t → lam ∸-helper · (succ n) · (succ zero ∸ succ n) ≡
                      t · (succ zero ∸ succ n))
               (beta ∸-helper (succ n))
               refl
      ⟩
    ∸-helper (succ n) · (succ zero ∸ succ n) ≡⟨ refl ⟩
    lam pred · (succ zero ∸ succ n)
      ≡⟨ beta pred (succ zero ∸ succ n) ⟩
    pred (succ zero ∸ succ n)
      ≡⟨ subst (λ t → pred (succ zero ∸ succ n) ≡ pred t)
               (∸-SS zN Nn)
               refl
      ⟩
    pred (zero ∸ n) ≡⟨ subst (λ t → pred (zero ∸ n) ≡ pred t)
                       (∸-0x Nn)
                       refl
                    ⟩
    pred zero       ≡⟨ pred-0 ⟩
    zero            ≡⟨ sym $ ∸-0S Nn ⟩
    zero ∸ succ n
  ∎

∸-SS (sN {m} Nm) (sN {n} Nn) =
  begin
    rec (succ (succ n)) (succ (succ m)) (lam ∸-helper)
      ≡⟨ rec-S (succ n) (succ (succ m)) (lam ∸-helper) ⟩
    lam ∸-helper · (succ n) · (succ (succ m) ∸ succ n)
      ≡⟨ subst (λ t → lam ∸-helper · (succ n) · (succ (succ m) ∸ succ n) ≡
                      t · (succ (succ m) ∸ succ n))
               (beta ∸-helper (succ n))
               refl
      ⟩
    ∸-helper (succ n) · (succ (succ m) ∸ succ n) ≡⟨ refl ⟩
    lam pred · (succ (succ m) ∸ succ n)
      ≡⟨ beta pred (succ (succ m) ∸ succ n) ⟩
    pred (succ (succ m) ∸ succ n)
      ≡⟨ subst (λ t → pred (succ (succ m) ∸ succ n) ≡ pred t)
               (∸-SS (sN Nm) Nn)
               refl
      ⟩
    pred (succ m ∸ n)       ≡⟨ sym $ beta pred (succ m ∸ n) ⟩
    lam pred · (succ m ∸ n) ≡⟨ refl ⟩
    ∸-helper n · (succ m ∸ n)
      ≡⟨ subst (λ t → ∸-helper n · (succ m ∸ n) ≡ t · (succ m ∸ n))
               (sym $ beta ∸-helper n)
               refl
      ⟩
    (lam ∸-helper) · n · (succ m ∸ n)
      ≡⟨ sym $ rec-S n (succ m) (lam ∸-helper) ⟩
    rec (succ n) (succ m) (lam ∸-helper) ≡⟨ refl ⟩
    succ m ∸ succ n
  ∎

*-0x : ∀ d → zero * d ≡ zero
*-0x d =
  begin
    rec zero zero (lam (*-helper₂ d)) ≡⟨ rec-0 zero ⟩
    zero
  ∎

*-Sx : ∀ d e → succ d * e ≡ e + d * e
*-Sx d e =
  begin
    rec (succ d) zero (lam (*-helper₂ e)) ≡⟨ rec-S d zero (lam (*-helper₂ e)) ⟩
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
        (subst (λ t → succ (n + zero) ≡ succ t)
               (+-rightIdentity Nn)
               refl
        )

+-N : ∀ {m n} → N m → N n → N (m + n)
+-N zN       Nn            = subst N (sym $ +-leftIdentity Nn) Nn
+-N {n = n} (sN {m} Nm) Nn = subst N (sym $ +-Sx m n) (sN (+-N Nm Nn))

+-assoc : ∀ {m n o} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} zN Nn No =
  begin
    zero + n + o ≡⟨ subst (λ t → zero + n + o ≡ t + o)
                          (+-leftIdentity Nn)
                          refl
                 ⟩
    n + o        ≡⟨ sym $ +-leftIdentity (+-N Nn No) ⟩
    zero + (n + o)
  ∎

+-assoc {n = n} {o} (sN {m} Nm) Nn No =
  begin
    succ m + n + o     ≡⟨ subst (λ t → succ m + n + o ≡ t + o)
                                (+-Sx m n)
                                refl
                       ⟩
    succ (m + n) + o   ≡⟨ +-Sx (m + n) o ⟩
    succ (m + n + o)   ≡⟨ subst (λ t → succ (m + n + o) ≡ succ t)
                                (+-assoc Nm Nn No)
                                refl
                       ⟩
    succ (m + (n + o)) ≡⟨ sym $ +-Sx m (n + o) ⟩
    succ m + (n + o)
  ∎

x+Sy≡S[x+y] : ∀ {m n} → N m → N n → m + succ n ≡ succ (m + n)
x+Sy≡S[x+y] {n = n} zN Nn =
  begin
    zero + succ n ≡⟨ +-0x (succ n) ⟩
    succ n        ≡⟨ subst (λ t → succ n ≡ succ t)
                           (sym $ +-leftIdentity Nn)
                           refl
                  ⟩
    succ (zero + n)
  ∎

x+Sy≡S[x+y] {n = n} (sN {m} Nm) Nn =
  begin
    succ m + succ n     ≡⟨ +-Sx m (succ n) ⟩
    succ (m + succ n)   ≡⟨ subst (λ t → succ (m + succ n) ≡ succ t)
                                 (x+Sy≡S[x+y] Nm Nn)
                                 refl
                        ⟩
    succ (succ (m + n)) ≡⟨ subst (λ t → succ (succ (m + n)) ≡ succ t)
                                 (sym $ +-Sx m n)
                                 refl
                        ⟩
    succ (succ m + n)
  ∎

[x+y]∸[x+z]≡y∸z : ∀ {m n o} → N m → N n → N o → (m + n) ∸ (m + o) ≡ n ∸ o
[x+y]∸[x+z]≡y∸z {n = n} {o} zN _ _ =
  begin
    (zero + n) ∸ (zero + o) ≡⟨ subst (λ t → (zero + n) ∸ (zero + o) ≡
                                            t ∸ (zero + o))
                                      (+-0x n) refl
                            ⟩
     n ∸ (zero + o)         ≡⟨ subst (λ t → n ∸ (zero + o) ≡ n ∸ t)
                                     (+-0x o)
                                     refl
                            ⟩
    n ∸ o
  ∎

[x+y]∸[x+z]≡y∸z {n = n} {o} (sN {m} Nm) Nn No =
  begin
    (succ m + n) ∸ (succ m + o) ≡⟨ subst (λ t → succ m + n ∸ (succ m + o) ≡
                                                t ∸ (succ m + o))
                                         (+-Sx m n)
                                         refl
                                ⟩
    succ (m + n) ∸ (succ m + o) ≡⟨ subst (λ t → succ (m + n) ∸ (succ m + o) ≡
                                                succ (m + n) ∸ t)
                                         (+-Sx m o)
                                         refl
                                ⟩
    succ (m + n) ∸ succ (m + o) ≡⟨ ∸-SS (+-N Nm Nn) (+-N Nm No) ⟩
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
    succ m + n   ≡⟨ +-Sx m n ⟩
    succ (m + n) ≡⟨ subst (λ t → succ (m + n) ≡ succ t)
                          (+-comm Nm Nn)
                          refl
                 ⟩
    succ (n + m) ≡⟨ sym $ x+Sy≡S[x+y] Nn Nm ⟩
    n + succ m
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

*-leftIdentity : ∀ {n} → N n → succ zero * n ≡ n
*-leftIdentity {n} Nn =
  begin
    succ zero * n ≡⟨ *-Sx zero n ⟩
    n + zero * n  ≡⟨ subst (λ t → n + zero * n ≡ n + t)
                           (*-leftZero n)
                           refl
                  ⟩
    n + zero      ≡⟨ +-rightIdentity Nn ⟩
    n
  ∎

x*Sy≡x+xy : ∀ {m n} → N m → N n → m * succ n ≡ m + m * n
x*Sy≡x+xy {n = n} zN _ = sym
  (
    begin
      zero + zero * n ≡⟨ subst (λ t → zero + zero * n ≡ zero + t)
                         (*-leftZero n)
                         refl
                      ⟩
      zero + zero     ≡⟨ +-leftIdentity zN ⟩
      zero            ≡⟨ sym $ *-leftZero (succ n) ⟩
      zero * succ n
    ∎
  )

x*Sy≡x+xy {n = n} (sN {m} Nm) Nn =
  begin
    succ m * succ n        ≡⟨ *-Sx m (succ n) ⟩
    succ n + m * succ n    ≡⟨ subst (λ t → succ n + m * succ n ≡ succ n + t)
                                    (x*Sy≡x+xy Nm Nn)
                                    refl
                           ⟩
    succ n + (m + m * n)   ≡⟨ +-Sx n (m + m * n) ⟩
    succ (n + (m + m * n)) ≡⟨ subst (λ t → succ (n + (m + m * n)) ≡ succ t)
                                    (sym $ +-assoc Nn Nm (*-N Nm Nn))
                                    refl
                           ⟩
    succ (n + m + m * n)   ≡⟨ subst (λ t → succ (n + m + m * n) ≡
                                           succ (t + m * n))
                                    (+-comm Nn Nm)
                                    refl
                           ⟩
     succ (m + n + m * n)  ≡⟨ subst (λ t → succ (m + n + m * n) ≡ succ t)
                                    (+-assoc Nm Nn (*-N Nm Nn))
                                    refl
                           ⟩

    succ (m + (n + m * n)) ≡⟨ sym $ +-Sx m (n + m * n) ⟩
    succ m + (n + m * n)   ≡⟨ subst (λ t → succ m + (n + m * n) ≡ succ m + t)
                                    (sym $ *-Sx m n)
                                    refl
                           ⟩
    succ m + succ m * n
    ∎

*-comm : ∀ {m n} → N m → N n → m * n ≡ n * m
*-comm {n = n} zN Nn          = trans (*-leftZero n) (sym $ *-rightZero Nn)
*-comm {n = n} (sN {m} Nm) Nn =
  begin
    succ m * n   ≡⟨ *-Sx m n ⟩
    n + m * n    ≡⟨ subst (λ t → n + m * n ≡ n + t)
                          (*-comm Nm Nn)
                          refl
                  ⟩
    n + n * m     ≡⟨ sym $ x*Sy≡x+xy Nn Nm ⟩
    n * succ m
  ∎

*∸-leftDistributive : ∀ {m n o} → N m → N n → N o → (m ∸ n) * o ≡ m * o ∸ n * o
*∸-leftDistributive {m} {o = o} _ zN _ =
  begin
    (m ∸ zero) * o   ≡⟨ subst (λ t → (m ∸ zero) * o ≡ t * o)
                              (∸-x0 m)
                              refl
                      ⟩
    m * o            ≡⟨ sym $ ∸-x0 (m * o) ⟩
    m * o ∸ zero     ≡⟨ subst (λ t → m * o ∸ zero ≡ m * o ∸ t)
                              (sym $ *-0x o)
                              refl
                     ⟩
    m * o ∸ zero * o
  ∎

*∸-leftDistributive {o = o} zN (sN {n} Nn) No =
  begin
    (zero ∸ succ n) * o  ≡⟨ subst (λ t → (zero ∸ succ n) * o ≡ t * o)
                                  (∸-0S Nn)
                                  refl
                         ⟩
    zero * o             ≡⟨ *-0x o ⟩
    zero                 ≡⟨ sym $ ∸-0x (*-N (sN Nn) No) ⟩
    zero ∸ succ n * o    ≡⟨ subst (λ t → zero ∸ succ n * o ≡ t ∸ succ n * o)
                                   (sym $ *-0x o)
                                   refl
                         ⟩
    zero * o ∸ succ n * o
  ∎

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) zN =
  begin
    (succ m ∸ succ n) * zero      ≡⟨ *-comm (∸-N (sN Nm) (sN Nn)) zN ⟩
    zero * (succ m ∸ succ n)      ≡⟨ *-0x (succ m ∸ succ n) ⟩
    zero                          ≡⟨ sym $ ∸-0x (*-N (sN Nn) zN) ⟩
    zero ∸ succ n * zero          ≡⟨ subst (λ t → zero ∸ succ n * zero ≡
                                                  t ∸ succ n * zero)
                                           (sym $ *-0x (succ m))
                                           refl
                                  ⟩
    zero * succ m ∸ succ n * zero ≡⟨ subst
                                       (λ t → zero * succ m ∸ succ n * zero ≡
                                              t ∸ succ n * zero)
                                       (*-comm zN (sN Nm))
                                       refl
                                  ⟩
    succ m * zero ∸ succ n * zero
  ∎

*∸-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  begin
    (succ m ∸ succ n) * succ o  ≡⟨ subst (λ t → (succ m ∸ succ n) * succ o ≡
                                                t * succ o)
                                         (∸-SS Nm Nn)
                                         refl
                                ⟩
    (m ∸ n) * succ o            ≡⟨ *∸-leftDistributive Nm Nn (sN No) ⟩
    m * succ o ∸ n * succ o     ≡⟨ sym $ [x+y]∸[x+z]≡y∸z (sN No)
                                                         (*-N Nm (sN No))
                                                         (*-N Nn (sN No))
                                ⟩
    (succ o + m * succ o) ∸ (succ o + n * succ o)
      ≡⟨ subst (λ t → (succ o + m * succ o) ∸ (succ o + n * succ o) ≡
                      t ∸ (succ o + n * succ o))
               (sym $ *-Sx m (succ o))
               refl
      ⟩
    (succ m * succ o) ∸ (succ o + n * succ o)
      ≡⟨ subst (λ t → (succ m * succ o) ∸ (succ o + n * succ o) ≡
                      (succ m * succ o) ∸ t)
               (sym $ *-Sx n (succ o))
               refl
      ⟩
    (succ m * succ o) ∸ (succ n * succ o)
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
    (zero + n) * succ o  ≡⟨ subst (λ t → (zero + n) * succ o ≡ t * succ o)
                                  (+-leftIdentity Nn)
                                  refl
                         ⟩
    n * succ o           ≡⟨ sym $ +-leftIdentity (*-N Nn (sN No)) ⟩
    zero + n * succ o    ≡⟨ subst (λ t → zero + n * succ o ≡ t +  n * succ o)
                                (sym $ *-0x (succ o))
                                refl
                         ⟩
    zero * succ o + n * succ o
  ∎

*+-leftDistributive (sN {m} Nm) zN (sN {o} No) =
 begin
    (succ m + zero) * succ o ≡⟨ subst (λ t → (succ m + zero) * succ o ≡
                                             t * succ o)
                                      (+-rightIdentity (sN Nm))
                                      refl
                              ⟩
    succ m * succ o          ≡⟨ sym $ +-rightIdentity (*-N (sN Nm) (sN No)) ⟩
    succ m * succ o + zero   ≡⟨ subst (λ t → succ m * succ o + zero ≡
                                             succ m * succ o + t)
                                      (sym $ *-leftZero (succ o))
                                      refl
                             ⟩
    succ m * succ o + zero * succ o
  ∎

*+-leftDistributive (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  begin
    (succ m + succ n) * succ o
      ≡⟨ subst (λ t → (succ m + succ n) * succ o ≡ t * succ o)
               (+-Sx m (succ n))
               refl
      ⟩
    succ (m + succ n) * succ o ≡⟨ *-Sx (m + succ n) (succ o) ⟩
    succ o + (m + succ n) * succ o
      ≡⟨ subst (λ t → succ o + (m + succ n) * succ o ≡ succ o + t)
               (*+-leftDistributive Nm (sN Nn) (sN No))
               refl
      ⟩
    succ o + (m * succ o + succ n * succ o)
      ≡⟨ sym $ +-assoc (sN No) (*-N Nm (sN No)) (*-N (sN Nn) (sN No)) ⟩
    succ o + m * succ o + succ n * succ o
      ≡⟨ subst (λ t → succ o + m * succ o + succ n * succ o ≡
                      t + succ n * succ o)
               (sym $ *-Sx m (succ o))
               refl
      ⟩
    succ m * succ o + succ n * succ o
      ∎
