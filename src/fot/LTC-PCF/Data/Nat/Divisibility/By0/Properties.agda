------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module LTC-PCF.Data.Nat.Divisibility.By0.Properties where

open import Common.FOL.Relation.Binary.EqReasoning

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Properties
open import LTC-PCF.Data.Nat.Divisibility.By0
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.Properties
open import LTC-PCF.Data.Nat.Properties
open import LTC-PCF.Data.Nat.UnaryNumbers
open import LTC-PCF.Data.Nat.UnaryNumbers.Totality

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : ∀ {n} → N n → succ₁ n ∣ zero
S∣0 {n} Nn = zero , nzero , sym (*-leftZero (succ₁ n))

-- 0 divides 0.
0∣0 : zero ∣ zero
0∣0 = zero , nzero , sym (*-leftZero zero)

-- The divisibility relation is reflexive.
∣-refl : ∀ {n} → N n → n ∣ n
∣-refl {n} Nn = [1] , 1-N , sym (*-leftIdentity Nn)

-- If x divides y and z then x divides y ∸ z.
x∣y→x∣z→x∣y∸z-helper : ∀ {m n o k k'} → N m → N k → N k' →
                       n ≡ k * m →
                       o ≡ k' * m →
                       n ∸ o ≡ (k ∸ k') * m
x∣y→x∣z→x∣y∸z-helper Nm Nk Nk' refl refl = sym (*∸-leftDistributive Nk Nk' Nm)

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z Nm Nn No (k , Nk , h₁) (k' , Nk' , h₂) =
  k ∸ k' , ∸-N Nk Nk' , x∣y→x∣z→x∣y∸z-helper Nm Nk Nk' h₁ h₂

-- If x divides y and z then x divides y + z.
x∣y→x∣z→x∣y+z-helper : ∀ {m n o k k'} → N m → N k → N k' →
                       n ≡ k * m →
                       o ≡ k' * m →
                       n + o ≡ (k + k') * m
x∣y→x∣z→x∣y+z-helper Nm Nk Nk' refl refl = sym (*+-leftDistributive Nk Nk' Nm)

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z Nm Nn No (k , Nk , h₁) (k' , Nk' , h₂) =
  k + k' , +-N Nk Nk' , x∣y→x∣z→x∣y+z-helper Nm Nk Nk' h₁ h₂

-- If x divides y and y is positive, then x ≤ y.
x∣S→x≤S : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → m ≤ succ₁ n
x∣S→x≤S {m} Nm Nn (.zero , nzero , Sn≡0*m) =
  ⊥-elim (0≢S (trans (sym (*-leftZero m)) (sym Sn≡0*m)))
x∣S→x≤S {m} Nm Nn (.(succ₁ k) , nsucc {k} Nk , Sn≡Sk*m) =
  subst (λ t₁ → m ≤ t₁)
        (sym Sn≡Sk*m)
        (subst (λ t₂ → m ≤ t₂)
               (sym (*-Sx k m))
               (x≤x+y Nm (*-N Nk Nm)))

0∣x→x≡0 : ∀ {m} → N m → zero ∣ m → m ≡ zero
0∣x→x≡0 nzero          _                 = refl
0∣x→x≡0 (nsucc {m} Nm) (k , Nk , Sm≡k*0) =
  ⊥-elim (0≢S (trans (sym (*-leftZero k))
                     (trans (*-comm nzero Nk) (sym Sm≡k*0))))
