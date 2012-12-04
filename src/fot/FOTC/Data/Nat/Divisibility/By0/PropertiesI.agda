------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.By0.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.Nat.Divisibility.By0
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityI

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : ∀ n → succ₁ n ∣ zero
S∣0 n = zero , nzero , sym (*-leftZero (succ₁ n))

-- 0 divides 0.
0∣0 : zero ∣ zero
0∣0 = zero , nzero , sym (*-leftZero zero)

-- The divisibility relation is reflexive.
∣-refl : ∀ {n} → N n → n ∣ n
∣-refl {n} Nn = [1] , 1-N , sym (*-leftIdentity Nn)

-- If x divides y and z then x divides y ∸ z.
x∣y→x∣z→x∣y∸z-helper : ∀ {m n o k₁ k₂} → N m → N k₁ → N k₂ →
                       n ≡ k₁ * m →
                       o ≡ k₂ * m →
                       n ∸ o ≡ (k₁ ∸ k₂) * m
x∣y→x∣z→x∣y∸z-helper {m} {n} {o} {k₁} {k₂} Nm Nk₁ Nk₂ h₁ h₂ =
  n ∸ o               ≡⟨ ∸-leftCong h₁ ⟩
  k₁ * m ∸ o          ≡⟨ ∸-rightCong h₂ ⟩
  (k₁ * m) ∸ (k₂ * m) ≡⟨ sym (*∸-leftDistributive Nk₁ Nk₂ Nm) ⟩
  (k₁ ∸ k₂) * m       ∎

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z Nm Nn No (k₁ , Nk₁ , h₁) (k₂ , Nk₂ , h₂) =
  k₁ ∸ k₂ , ∸-N Nk₁ Nk₂ , x∣y→x∣z→x∣y∸z-helper Nm Nk₁ Nk₂ h₁ h₂

-- If x divides y and z then x divides y + z.
x∣y→x∣z→x∣y+z-helper : ∀ {m n o k₁ k₂} → N m → N k₁ → N k₂ →
                       n ≡ k₁ * m →
                       o ≡ k₂ * m →
                       n + o ≡ (k₁ + k₂) * m
x∣y→x∣z→x∣y+z-helper {m} {n} {o} {k₁} {k₂} Nm Nk₁ Nk₂ h₁ h₂ =
  n + o               ≡⟨ +-leftCong h₁ ⟩
  k₁ * m + o          ≡⟨ +-rightCong h₂ ⟩
  (k₁ * m) + (k₂ * m) ≡⟨ sym (*+-leftDistributive Nk₁ Nk₂ Nm) ⟩
  (k₁ + k₂) * m       ∎

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z Nm Nn No (k₁ , Nk₁ , h₁) (k₂ , Nk₂ , h₂) =
  k₁ + k₂ , +-N Nk₁ Nk₂ , x∣y→x∣z→x∣y+z-helper Nm Nk₁ Nk₂ h₁ h₂

-- If x divides y, and y is positive, then x ≤ y.
x∣S→x≤S : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → m ≤ succ₁ n
x∣S→x≤S {m} Nm Nn (.zero , nzero , Sn≡0*m) =
  ⊥-elim (0≢S (trans (sym (*-leftZero m)) (sym Sn≡0*m)))
x∣S→x≤S {m} Nm Nn (.(succ₁ k) , nsucc {k} Nk , Sn≡Sk*m) =
  subst (λ t₁ → m ≤ t₁)
        (sym Sn≡Sk*m)
        (subst (λ t₂ → m ≤ t₂)
               (sym (*-Sx k m))
               (x≤x+y Nm (*-N Nk Nm)))

-- If 0 divides x, then x = 0.
0∣x→x≡0 : ∀ {m} → N m → zero ∣ m → m ≡ zero
0∣x→x≡0 nzero          _                 = refl
0∣x→x≡0 (nsucc {m} Nm) (k , Nk , Sm≡k*0) =
  ⊥-elim (0≢S (trans (sym (*-leftZero k))
                     (trans (*-comm nzero Nk) (sym Sm≡k*0))))
