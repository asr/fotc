------------------------------------------------------------------------------
-- Arithmetic properties using equational reasoning
------------------------------------------------------------------------------

module LTC.Function.Arithmetic.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import LTC.Data.N
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.Properties
  using ( +-leftIdentity ; *-leftZero ; *-comm ; minus-0x )

open import MyStdLib.Function
import MyStdLib.Relation.Binary.EqReasoning
open module APER = MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

------------------------------------------------------------------------------
-- Closure properties

pred-N : {n : D} → N n → N (pred n)
pred-N zN          = subst (λ t → N t) (sym cP₁) zN
pred-N (sN {n} Nn) = subst (λ t → N t) (sym (cP₂ n)) Nn

minus-N : {m n : D} → N m → N n → N (m - n)
minus-N {m} Nm zN                   = subst (λ t → N t) (sym (minus-x0 m)) Nm
minus-N     zN (sN {n} Nn)          = subst (λ t → N t) (sym (minus-0S n)) zN
minus-N     (sN {m} Nm) (sN {n} Nn) = subst (λ t → N t)
                                            (sym (minus-SS m n))
                                            (minus-N Nm Nn)

+-N : {m n : D} → N m → N n → N (m + n)
+-N zN Nn = subst (λ t → N t) (sym (+-leftIdentity Nn)) Nn
+-N {n = n} (sN {m} Nm ) Nn =
  subst ((λ t → N t)) (sym (+-Sx m n)) (sN (+-N Nm Nn))

*-N : {m n : D} → N m → N n → N (m * n)
*-N zN Nn = subst (λ t → N t) (sym (*-leftZero Nn)) zN
*-N {n = n} (sN {m} Nm) Nn =
  subst (λ t → N t) (sym (*-Sx m n)) (+-N Nn (*-N Nm Nn))

------------------------------------------------------------------------------

[x+y]-[x+z]≡y-z : {m n o : D} → N m → N n → N o →
                  (m + n) - (m + o) ≡ n - o
[x+y]-[x+z]≡y-z {n = n} {o = o} zN Nn No =
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

[x+y]-[x+z]≡y-z {n = n} {o = o} (sN {m} Nm) Nn No =
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
    succ (m + n) - succ (m + o) ≡⟨ minus-SS (m + n) (m + o) ⟩
    (m + n) - (m + o) ≡⟨ [x+y]-[x+z]≡y-z Nm Nn No ⟩
    n - o
  ∎

[x-y]z≡xz*yz : {m n o : D} → N m → N n → N o → (m - n) * o ≡ m * o - n * o
[x-y]z≡xz*yz {m} .{zero} {o} Nm zN No =
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
                                  (minus-0S n)
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
                                         (minus-SS m n)
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
