------------------------------------------------------------------------------
-- Arithmetic properties using equational reasoning
------------------------------------------------------------------------------

module LTC.Function.Arithmetic.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import LTC.Data.N
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.Properties
  using ( +-leftIdentity ; *-leftZero  )

open import MyStdLib.Function
import MyStdLib.Relation.Binary.EqReasoning
open module APER = MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

------------------------------------------------------------------------------
-- Closure properties

pred-N : {n : D} → N n → N (pred n)
pred-N zN          = subst (λ t → N t) (sym cP₁) zN
pred-N (sN {n} Nn) = subst (λ t → N t) (sym (cP₂ n)) Nn

minus-N : {m n : D} → N m → N n → N (m - n)
minus-N {m} Nm zN = subst (λ t → N t) (sym (minus-x0 m)) Nm
minus-N {m} Nm (sN {n} Nn) =
  subst (λ t → N t) (sym (minus-xS m n)) (pred-N (minus-N Nm Nn))

+-N : {m n : D} → N m → N n → N (m + n)
+-N zN Nn = subst (λ t → N t) (sym (+-leftIdentity Nn)) Nn
+-N {n = n} (sN {m} Nm ) Nn =
  subst ((λ t → N t)) (sym (+-Sx m n)) (sN (+-N Nm Nn))

*-N : {m n : D} → N m → N n → N (m * n)
*-N zN Nn = subst (λ t → N t) (sym (*-leftZero Nn)) zN
*-N {n = n} (sN {m} Nm) Nn =
  subst (λ t → N t) (sym (*-Sx m n)) (+-N Nn (*-N Nm Nn))

----------------------------------------------------------------------------

{-
-- Left identify for addition using the induction principle for N.
addLeftIdentity2 : {n : D} → N n → zero + n ≡ n
addLeftIdentity2 = indN (λ i → P i) P0 iStep
  where
    P : D → Set
    P i = zero + i ≡ i

    P0 : P zero
    P0 = add-x0 zero

    iStep : {i : D} → N i → P i → P (succ i)
    iStep {i} Ni Pi =
      begin
        zero + succ i   ≡⟨ add-xS zero i ⟩
        succ (zero + i) ≡⟨ subst (λ t → succ (zero + i) ≡ succ t)
                                 Pi
                                 refl
                        ⟩
        succ i
      ∎

----------------------------------------------------------------------------
-- Associativity of addition using pattern matching.
addAssoc1 : (m n o : D) → N m → N n → N o → m + n + o ≡ m + (n + o)
addAssoc1 m n .zero _ _ zN =
  begin
    m + n + zero ≡⟨ add-x0 (m + n) ⟩
    m + n        ≡⟨ subst (λ t → m + t ≡ m + (n + zero))
                          (add-x0 n)
                          refl
                 ⟩
    m + (n + zero)
  ∎

addAssoc1 m n .(succ o) Nm Nn (sN {o} No) =
  begin
    (m + n) + (succ o) ≡⟨ add-xS (m + n) o ⟩
    succ (m + n + o)   ≡⟨ subst (λ t → succ t ≡ succ (m + (n + o)))
                                (sym (addAssoc1 m n o Nm Nn No))
                                refl
                       ⟩
    succ (m + (n + o)) ≡⟨ sym (add-xS m (n + o)) ⟩
    m + (succ (n + o)) ≡⟨ subst (λ t → m + t ≡ m + (n + succ o))
                                (add-xS n o)
                                refl
                       ⟩
    m + (n + succ o)
  ∎

-- Associativity of addition using the induction principle for N.
addAssoc2 : {m n o : D} → N m → N n → N o → m + n + o ≡ m + (n + o)
addAssoc2 {m} {n} _ _ No = indN (λ o → P o) P0 iStep No
  where
    P : D → Set
    P i = m + n + i ≡ m + (n + i)

    P0 : P zero
    P0 =
       begin
         m + n + zero ≡⟨ add-x0 (m + n) ⟩
         m + n        ≡⟨ subst (λ t → m + t ≡ m + (n + zero))
                               (add-x0 n)
                               refl
                      ⟩
         m + (n + zero)
       ∎

    iStep : {i : D} → N i → P i → P (succ i)
    iStep {i} Ni Pi =
      begin
        m + n + succ i     ≡⟨ add-xS (m + n) i ⟩
        succ (m + n + i)   ≡⟨ subst (λ t → succ t ≡
                                           succ (m + (n + i)))
                                    (sym Pi)
                                    refl
                           ⟩
        succ (m + (n + i)) ≡⟨ sym (add-xS m (n + i)) ⟩
        m + (succ (n + i)) ≡⟨ subst (λ t → m + t ≡
                                           m + (n + succ i))
                                    (add-xS n i)
                                    refl
                           ⟩
        m + (n + succ i)
      ∎
-}

-- *-leftZero : {n : D} → N n → zero * n ≡ zero
-- *-leftZero zN          = *-x0 zero
-- *-leftZero (sN {n} Nn) =
--   begin
--     zero * succ n   ≡⟨ *-xS zero n ⟩
--     zero * n + zero ≡⟨ subst (λ t → t + zero ≡ zero + zero)
--                              (sym (*-leftZero Nn))
--                              refl
--                      ⟩
--     zero + zero     ≡⟨ +-leftIdentity zN ⟩
--     zero
--   ∎

-- postulate
--   mn+n≡m+1*n : (m n : D) → m * n + n ≡ succ m * n

-- *-comm : {m n : D} → N m → N n → m * n ≡ n * m
-- *-comm Nm zN = trans (*-rightZero Nm) $ sym $ *-leftZero Nm
-- *-comm {m} Nm (sN {n} Nn) =
--   begin
--     m * succ n   ≡⟨ *-xS m n ⟩
--     m * n + m    ≡⟨ subst (λ t → t + m ≡ n * m + m)
--                           (*-comm Nn Nm)
--                           refl
--                   ⟩
--     n * m + m     ≡⟨  mn+n≡m+1*n n m ⟩
--     succ n * m
--   ∎
