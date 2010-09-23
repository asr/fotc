------------------------------------------------------------------------------
-- Arithmetic properties (using equational reasoning)
------------------------------------------------------------------------------

module LTC-PCF.DataPCF.NatPCF.PropertiesPCF-ER where

open import LTC.Minimal
open import LTC.MinimalER using ( subst )

open import LTC-PCF.DataPCF.NatPCF
  using ( _+_ ; +-aux
        ; _-_ ; minus-aux
        ; _*_ ; *-aux₁ ; *-aux₂
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.DataPCF.NatPCF.RecPCF using ( rec )
open import LTC-PCF.DataPCF.NatPCF.RecPCF.PropertiesPCF using ( rec-0 ; rec-S )

-- open import MyStdLib.Function
import MyStdLib.Relation.Binary.EqReasoning
open module NatPCF-ER =
  MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

------------------------------------------------------------------------------

+-0x : (d : D) → zero + d ≡ d
+-0x d =
  begin
    rec zero d (lam +-aux) ≡⟨ rec-0 d ⟩
    d
  ∎

+-Sx : (d e : D) → succ d + e ≡ succ (d + e)
+-Sx d e =
  begin
    rec (succ d) e (lam +-aux) ≡⟨ rec-S d e (lam +-aux) ⟩
    lam +-aux ∙ d ∙ (d + e)    ≡⟨ subst (λ t → lam +-aux ∙ d ∙ (d + e) ≡
                                               t ∙ (d + e))
                                         (cBeta +-aux d)
                                         refl
                                ⟩
    +-aux d ∙ (d + e)           ≡⟨ refl ⟩
    lam succ ∙ (d + e)          ≡⟨ cBeta succ (d + e) ⟩
    succ (d + e)
  ∎

minus-x0 : (d : D) → d - zero ≡ d
minus-x0 d =
  begin
    rec zero d (lam minus-aux) ≡⟨ rec-0 d ⟩
    d
  ∎

minus-0S : {n : D} → N n → zero - succ n ≡ zero
minus-0S zN =
  begin
    rec (succ zero) zero (lam minus-aux) ≡⟨ rec-S zero zero (lam minus-aux) ⟩
    lam minus-aux ∙ zero ∙ (zero - zero)
      ≡⟨ subst (λ t → lam minus-aux ∙ zero ∙ (zero - zero) ≡
                      t ∙ (zero - zero))
               (cBeta minus-aux zero)
               refl
      ⟩
    minus-aux zero ∙ (zero - zero) ≡⟨ refl ⟩
    lam pred ∙ (zero - zero)       ≡⟨ cBeta pred (zero - zero) ⟩
    pred (zero - zero)             ≡⟨ subst (λ t → pred (zero - zero) ≡
                                                   pred t)
                                            (minus-x0 zero)
                                            refl
                                   ⟩
    pred zero                      ≡⟨ cP₁ ⟩
    zero
  ∎

minus-0S (sN {n} Nn) =
  begin
    rec (succ (succ n)) zero (lam minus-aux)
      ≡⟨ rec-S (succ n) zero (lam minus-aux) ⟩
    lam minus-aux ∙ (succ n) ∙ (zero - (succ n))
      ≡⟨ subst (λ t → lam minus-aux ∙ (succ n) ∙ (zero - (succ n)) ≡
                      t ∙ (zero - (succ n)))
               (cBeta minus-aux (succ n))
               refl
      ⟩
    minus-aux (succ n) ∙ (zero - (succ n)) ≡⟨ refl ⟩
    lam pred ∙ (zero - (succ n))
      ≡⟨ cBeta pred (zero - (succ n)) ⟩
    pred (zero - (succ n)) ≡⟨ subst (λ t → pred (zero - (succ n)) ≡ pred t)
                                    (minus-0S Nn)
                                    refl
                           ⟩
    pred zero              ≡⟨ cP₁ ⟩
    zero
  ∎

minus-0x : {n : D} → N n → zero - n ≡ zero
minus-0x zN      = minus-x0 zero
minus-0x (sN Nn) = minus-0S Nn

minus-SS : {m n : D} → N m → N n → succ m - succ n ≡ m - n
minus-SS {m} _ zN =
  begin
    rec (succ zero) (succ m) (lam minus-aux)
      ≡⟨ rec-S zero (succ m) (lam minus-aux) ⟩
    lam minus-aux ∙ zero ∙ (succ m - zero)
      ≡⟨ subst (λ t → lam minus-aux ∙ zero ∙ (succ m - zero) ≡
                      t ∙ (succ m - zero))
               (cBeta minus-aux zero)
               refl
      ⟩
    minus-aux zero ∙ (succ m - zero) ≡⟨ refl ⟩
    lam pred ∙ (succ m - zero)       ≡⟨ cBeta pred (succ m - zero) ⟩
    pred (succ m - zero)             ≡⟨ subst (λ t → pred (succ m - zero) ≡
                                                     pred t)
                                              (minus-x0 (succ m))
                                              refl
                                     ⟩
    pred (succ m)                    ≡⟨ cP₂ m  ⟩
    m                                ≡⟨ sym (minus-x0 m)  ⟩
    m - zero
  ∎

minus-SS zN (sN {n} Nn) =
  begin
    rec (succ (succ n)) (succ zero) (lam minus-aux)
      ≡⟨ rec-S (succ n) (succ zero) (lam minus-aux) ⟩
    lam minus-aux ∙ (succ n) ∙ (succ zero - succ n)
      ≡⟨ subst (λ t → lam minus-aux ∙ (succ n) ∙ (succ zero - succ n) ≡
                      t ∙ (succ zero - succ n))
               (cBeta minus-aux (succ n))
               refl
      ⟩
    minus-aux (succ n) ∙ (succ zero - succ n) ≡⟨ refl ⟩
    lam pred ∙ (succ zero - succ n)
      ≡⟨ cBeta pred (succ zero - succ n) ⟩
    pred (succ zero - succ n)
      ≡⟨ subst (λ t → pred (succ zero - succ n) ≡ pred t)
               (minus-SS zN Nn)
               refl
      ⟩
    pred (zero - n) ≡⟨ subst (λ t → pred (zero - n) ≡ pred t)
                       (minus-0x Nn)
                       refl
                    ⟩
    pred zero       ≡⟨ cP₁  ⟩
    zero            ≡⟨ sym (minus-0S Nn)  ⟩
    zero - succ n
  ∎

minus-SS (sN {m} Nm) (sN {n} Nn) =
  begin
    rec (succ (succ n)) (succ (succ m)) (lam minus-aux)
      ≡⟨ rec-S (succ n) (succ (succ m)) (lam minus-aux) ⟩
    lam minus-aux ∙ (succ n) ∙ (succ (succ m) - succ n)
      ≡⟨ subst (λ t → lam minus-aux ∙ (succ n) ∙ (succ (succ m) - succ n) ≡
                      t ∙ (succ (succ m) - succ n))
               (cBeta minus-aux (succ n))
               refl
      ⟩
    minus-aux (succ n) ∙ (succ (succ m) - succ n) ≡⟨ refl ⟩
    lam pred ∙ (succ (succ m) - succ n)
      ≡⟨ cBeta pred (succ (succ m) - succ n) ⟩
    pred (succ (succ m) - succ n)
      ≡⟨ subst (λ t → pred (succ (succ m) - succ n) ≡ pred t)
               (minus-SS (sN Nm) Nn)
               refl
      ⟩
    pred (succ m - n)       ≡⟨ sym (cBeta pred (succ m - n)) ⟩
    lam pred ∙ (succ m - n) ≡⟨ refl  ⟩
    minus-aux n ∙ (succ m - n)
      ≡⟨ subst (λ t → minus-aux n ∙ (succ m - n) ≡ t ∙ (succ m - n))
               (sym (cBeta minus-aux n))
               refl
      ⟩
    (lam minus-aux) ∙ n ∙ (succ m - n)
      ≡⟨ sym (rec-S n (succ m) (lam minus-aux)) ⟩
    rec (succ n) (succ m) (lam minus-aux) ≡⟨ refl  ⟩
    succ m - succ n
  ∎

*-0x : (d : D) → zero * d ≡ zero
*-0x d =
  begin
    rec zero zero (lam (*-aux₂ d)) ≡⟨ rec-0 zero ⟩
    zero
  ∎

*-Sx : (d e : D) → succ d * e ≡ e + d * e
*-Sx d e =
  begin
    rec (succ d) zero (lam (*-aux₂ e)) ≡⟨ rec-S d zero (lam (*-aux₂ e)) ⟩
    lam (*-aux₂ e) ∙ d ∙ (d * e)
      ≡⟨ subst (λ t → lam (*-aux₂ e) ∙ d ∙ (d * e) ≡ t ∙ (d * e))
               (cBeta (*-aux₂ e) d)
               refl
      ⟩
    *-aux₂ e d ∙ (d * e)     ≡⟨ refl ⟩
    lam (*-aux₁ e) ∙ (d * e) ≡⟨ cBeta (*-aux₁ e) (d * e) ⟩
    *-aux₁ e (d * e)         ≡⟨ refl ⟩
    e + (d * e)
  ∎

minus-N : {m n : D} → N m → N n → N (m - n)
minus-N {m} Nm       zN     = subst N (sym (minus-x0 m)) Nm
minus-N     zN      (sN Nn) = subst N (sym (minus-0S Nn)) zN
minus-N     (sN Nm) (sN Nn) = subst N (sym (minus-SS Nm Nn)) (minus-N Nm Nn)

+-leftIdentity : {n : D} → N n → zero + n ≡ n
+-leftIdentity {n} _ = +-0x n

+-rightIdentity : {n : D} → N n → n + zero ≡ n
+-rightIdentity zN          = +-leftIdentity zN
+-rightIdentity (sN {n} Nn) =
  trans (+-Sx n zero)
        (subst (λ t → succ (n + zero) ≡ succ t)
               (+-rightIdentity Nn)
               refl
        )

+-N : {m n : D} → N m → N n → N (m + n)
+-N zN       Nn            = subst N (sym (+-leftIdentity Nn)) Nn
+-N {n = n} (sN {m} Nm) Nn = subst N (sym (+-Sx m n)) (sN (+-N Nm Nn))

+-assoc : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
+-assoc {n = n} {o} zN Nn No =
  begin
    zero + n + o ≡⟨ subst (λ t → zero + n + o ≡ t + o)
                          (+-leftIdentity Nn)
                          refl
                 ⟩
    n + o        ≡⟨ sym (+-leftIdentity (+-N Nn No)) ⟩
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
    succ (m + (n + o)) ≡⟨ sym (+-Sx m (n + o)) ⟩
    succ m + (n + o)
  ∎

x+1+y≡1+x+y : {m n : D} → N m → N n → m + succ n ≡ succ (m + n)
x+1+y≡1+x+y {n = n} zN Nn =
  begin
    zero + succ n ≡⟨ +-0x (succ n) ⟩
    succ n        ≡⟨ subst (λ t → succ n ≡ succ t)
                           (sym (+-leftIdentity Nn))
                           refl
                  ⟩
    succ (zero + n)
  ∎

x+1+y≡1+x+y {n = n} (sN {m} Nm) Nn =
  begin
    succ m + succ n     ≡⟨ +-Sx m (succ n) ⟩
    succ (m + succ n)   ≡⟨ subst (λ t → succ (m + succ n) ≡ succ t)
                                 (x+1+y≡1+x+y Nm Nn)
                                 refl
                        ⟩
    succ (succ (m + n)) ≡⟨ subst (λ t → succ (succ (m + n)) ≡ succ t)
                                 (sym (+-Sx m n))
                                 refl
                        ⟩
    succ (succ m + n)
  ∎

[x+y]-[x+z]≡y-z : {m n o : D} → N m → N n → N o →
                  (m + n) - (m + o) ≡ n - o
[x+y]-[x+z]≡y-z {n = n} {o} zN _ _ =
  begin
    (zero + n) - (zero + o) ≡⟨ subst (λ t → (zero + n) - (zero + o) ≡
                                            t - (zero + o))
                                      (+-0x n) refl
                            ⟩
     n - (zero + o)         ≡⟨ subst (λ t → n - (zero + o) ≡ n - t)
                                     (+-0x o)
                                     refl ⟩
    n - o
  ∎

[x+y]-[x+z]≡y-z {n = n} {o} (sN {m} Nm) Nn No =
  begin
    (succ m + n) - (succ m + o) ≡⟨ subst (λ t → succ m + n - (succ m + o) ≡
                                                t - (succ m + o))
                                         (+-Sx m n)
                                         refl
                                ⟩
    succ (m + n) - (succ m + o) ≡⟨ subst (λ t → succ (m + n) - (succ m + o) ≡
                                                succ (m + n) - t)
                                         (+-Sx m o)
                                         refl ⟩
    succ (m + n) - succ (m + o) ≡⟨ minus-SS (+-N Nm Nn) (+-N Nm No) ⟩
    (m + n) - (m + o) ≡⟨ [x+y]-[x+z]≡y-z Nm Nn No ⟩
    n - o
  ∎

+-comm : {m n : D} → N m → N n → m + n ≡ n + m
+-comm {n = n} zN Nn =
  begin
    zero + n ≡⟨ +-leftIdentity Nn ⟩
    n        ≡⟨ sym (+-rightIdentity Nn) ⟩
    n + zero
   ∎

+-comm {n = n} (sN {m} Nm) Nn =
  begin
    succ m + n   ≡⟨ +-Sx m n ⟩
    succ (m + n) ≡⟨ subst (λ t → succ (m + n) ≡ succ t)
                          (+-comm Nm Nn)
                          refl ⟩
    succ (n + m) ≡⟨ sym (x+1+y≡1+x+y Nn Nm) ⟩
    n + succ m
   ∎

*-leftZero : (n : D) → zero * n ≡ zero
*-leftZero = *-0x

*-N : {m n : D} → N m → N n → N (m * n)
*-N {n = n} zN          _  = subst N (sym (*-leftZero n)) zN
*-N {n = n} (sN {m} Nm) Nn = subst N (sym (*-Sx m n)) (+-N Nn (*-N Nm Nn))

*-rightZero : {n : D} → N n → n * zero ≡ zero
*-rightZero zN          = *-leftZero zero
*-rightZero (sN {n} Nn) =
  trans (*-Sx n zero)
        (trans (+-leftIdentity (*-N Nn zN)) (*-rightZero Nn))

*-leftIdentity : {n : D} → N n → succ zero * n ≡ n
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

x*1+y≡x+xy : {m n : D} → N m → N n → m * succ n ≡ m + m * n
x*1+y≡x+xy {n = n} zN _ = sym
  (
    begin
      zero + zero * n ≡⟨ subst (λ t → zero + zero * n ≡ zero + t)
                         (*-leftZero n)
                         refl
                      ⟩
      zero + zero     ≡⟨ +-leftIdentity zN ⟩
      zero            ≡⟨ sym (*-leftZero (succ n)) ⟩
      zero * succ n
    ∎
  )

x*1+y≡x+xy {n = n} (sN {m} Nm) Nn =
  begin
    succ m * succ n        ≡⟨ *-Sx m (succ n) ⟩
    succ n + m * succ n    ≡⟨ subst (λ t → succ n + m * succ n ≡ succ n + t)
                                    (x*1+y≡x+xy Nm Nn)
                                    refl
                           ⟩
    succ n + (m + m * n)   ≡⟨ +-Sx n (m + m * n) ⟩
    succ (n + (m + m * n)) ≡⟨ subst (λ t → succ (n + (m + m * n)) ≡ succ t)
                                    (sym (+-assoc Nn Nm (*-N Nm Nn)))
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

    succ (m + (n + m * n)) ≡⟨ sym (+-Sx m (n + m * n)) ⟩
    succ m + (n + m * n)   ≡⟨ subst (λ t → succ m + (n + m * n) ≡ succ m + t)
                                    (sym (*-Sx m n))
                                    refl
                           ⟩
    succ m + succ m * n
    ∎

*-comm : {m n : D} → N m → N n → m * n ≡ n * m
*-comm {n = n} zN Nn          = trans (*-leftZero n) (sym (*-rightZero Nn))
*-comm {n = n} (sN {m} Nm) Nn =
  begin
    succ m * n   ≡⟨ *-Sx m n ⟩
    n + m * n    ≡⟨ subst (λ t → n + m * n ≡ n + t)
                          (*-comm Nm Nn)
                          refl
                  ⟩
    n + n * m     ≡⟨ sym (x*1+y≡x+xy Nn Nm) ⟩
    n * succ m
  ∎

[x-y]z≡xz*yz : {m n o : D} → N m → N n → N o → (m - n) * o ≡ m * o - n * o
[x-y]z≡xz*yz {m} {o = o} _ zN _ =
  begin
    (m - zero) * o   ≡⟨ subst (λ t → (m - zero) * o ≡ t * o)
                              (minus-x0 m)
                              refl
                      ⟩
    m * o            ≡⟨ sym (minus-x0 (m * o)) ⟩
    m * o - zero     ≡⟨ subst (λ t → m * o - zero ≡ m * o - t)
                              (sym (*-0x o))
                              refl
                     ⟩
    m * o - zero * o
  ∎

[x-y]z≡xz*yz {o = o} zN (sN {n} Nn) No =
  begin
    (zero - succ n) * o  ≡⟨ subst (λ t → (zero - succ n) * o ≡ t * o)
                                  (minus-0S Nn)
                                  refl
                         ⟩
    zero * o             ≡⟨ *-0x o ⟩
    zero                 ≡⟨ sym (minus-0x (*-N (sN Nn) No)) ⟩
    zero - succ n * o    ≡⟨ subst (λ t → zero - succ n * o ≡ t - succ n * o)
                                   (sym (*-0x o))
                                   refl
                         ⟩
    zero * o - succ n * o
  ∎

[x-y]z≡xz*yz (sN {m} Nm) (sN {n} Nn) zN =
  begin
    (succ m - succ n) * zero      ≡⟨ *-comm (minus-N (sN Nm) (sN Nn)) zN ⟩
    zero * (succ m - succ n)      ≡⟨ *-0x (succ m - succ n) ⟩
    zero                          ≡⟨ sym (minus-0x (*-N (sN Nn) zN)) ⟩
    zero - succ n * zero          ≡⟨ subst (λ t → zero - succ n * zero ≡
                                                  t - succ n * zero)
                                           (sym (*-0x (succ m)))
                                           refl
                                  ⟩
    zero * succ m - succ n * zero ≡⟨ subst
                                       (λ t → zero * succ m - succ n * zero ≡
                                              t - succ n * zero)
                                       (*-comm zN (sN Nm))
                                       refl
                                  ⟩
    succ m * zero - succ n * zero
  ∎

[x-y]z≡xz*yz (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  begin
    (succ m - succ n) * succ o  ≡⟨ subst (λ t → (succ m - succ n) * succ o ≡
                                                t * succ o)
                                         (minus-SS Nm Nn)
                                         refl
                                ⟩
    (m - n) * succ o            ≡⟨ [x-y]z≡xz*yz Nm Nn (sN No) ⟩
    m * succ o - n * succ o     ≡⟨ sym ([x+y]-[x+z]≡y-z (sN No)
                                                        (*-N Nm (sN No))
                                                        (*-N Nn (sN No)))
                                ⟩
    (succ o + m * succ o) - (succ o + n * succ o)
      ≡⟨ subst (λ t → (succ o + m * succ o) - (succ o + n * succ o) ≡
                      t - (succ o + n * succ o))
               (sym (*-Sx m (succ o)))
               refl
      ⟩
    (succ m * succ o) - (succ o + n * succ o)
      ≡⟨ subst (λ t → (succ m * succ o) - (succ o + n * succ o) ≡
                      (succ m * succ o) - t)
               (sym (*-Sx n (succ o)))
               refl
      ⟩
    (succ m * succ o) - (succ n * succ o)
  ∎

[x+y]z≡xz*yz : {m n o : D} → N m → N n → N o → (m + n) * o ≡ m * o + n * o
[x+y]z≡xz*yz {m} {n} Nm Nn zN =
  begin
    (m + n) * zero       ≡⟨ *-comm (+-N Nm Nn) zN ⟩
    zero * (m + n)       ≡⟨ *-0x (m + n) ⟩
    zero                 ≡⟨ sym (*-0x m) ⟩
    zero * m             ≡⟨ *-comm zN Nm ⟩
    m * zero             ≡⟨ sym (+-rightIdentity (*-N Nm zN)) ⟩
    m * zero + zero      ≡⟨ subst (λ t → m * zero + zero ≡ m * zero + t)
                                  (trans (sym (*-0x n)) (*-comm zN Nn))
                                  refl
                         ⟩
    m * zero + n * zero
  ∎

[x+y]z≡xz*yz {n = n} zN Nn (sN {o} No) =
  begin
    (zero + n) * succ o  ≡⟨ subst (λ t → (zero + n) * succ o ≡ t * succ o)
                                  (+-leftIdentity Nn)
                                  refl
                         ⟩
    n * succ o           ≡⟨ sym (+-leftIdentity (*-N Nn (sN No))) ⟩
    zero + n * succ o    ≡⟨ subst (λ t → zero + n * succ o ≡ t +  n * succ o)
                                (sym (*-0x (succ o)))
                                refl
                         ⟩
    zero * succ o + n * succ o
  ∎

[x+y]z≡xz*yz (sN {m} Nm) zN (sN {o} No) =
 begin
    (succ m + zero) * succ o ≡⟨ subst (λ t → (succ m + zero) * succ o ≡
                                             t * succ o)
                                      (+-rightIdentity (sN Nm))
                                      refl
                              ⟩
    succ m * succ o          ≡⟨ sym (+-rightIdentity (*-N (sN Nm) (sN No))) ⟩
    succ m * succ o + zero   ≡⟨ subst (λ t → succ m * succ o + zero ≡
                                             succ m * succ o + t)
                                      (sym (*-leftZero (succ o)))
                                      refl
                             ⟩
    succ m * succ o + zero * succ o
  ∎

[x+y]z≡xz*yz (sN {m} Nm) (sN {n} Nn) (sN {o} No) =
  begin
    (succ m + succ n) * succ o
      ≡⟨ subst (λ t → (succ m + succ n) * succ o ≡ t * succ o)
               (+-Sx m (succ n))
               refl
      ⟩
    succ (m + succ n) * succ o ≡⟨ *-Sx (m + succ n) (succ o) ⟩
    succ o + (m + succ n) * succ o
      ≡⟨ subst (λ t → succ o + (m + succ n) * succ o ≡ succ o + t)
               ([x+y]z≡xz*yz Nm (sN Nn) (sN No))
               refl
      ⟩
    succ o + (m * succ o + succ n * succ o)
      ≡⟨ sym (+-assoc (sN No) (*-N Nm (sN No)) (*-N (sN Nn) (sN No))) ⟩
    succ o + m * succ o + succ n * succ o
      ≡⟨ subst (λ t → succ o + m * succ o + succ n * succ o ≡
                      t + succ n * succ o)
               (sym (*-Sx m (succ o)))
               refl
      ⟩
    succ m * succ o + succ n * succ o
      ∎
