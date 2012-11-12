------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.Properties
open import FOTC.Data.Nat
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.Nat.Divisibility.NotBy0
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : ∀ n → succ₁ n ∣ zero
S∣0 n = S≢0 , zero , nzero , sym (*-leftZero (succ₁ n))

-- 0 doesn't divide any number.
0∤x : ∀ {n} → ¬ (zero ∣ n)
0∤x (0≢0 , _) = ⊥-elim (0≢0 refl)

-- The divisibility relation is reflexive for positive numbers.
∣-refl-S : ∀ {n} → N n → succ₁ n ∣ succ₁ n
∣-refl-S {n} Nn =
  S≢0 , succ₁ zero , nsucc nzero , sym (*-leftIdentity (nsucc Nn))

-- If x divides y and z then x divides y ∸ z.
x∣y→x∣z→x∣y∸z-helper : ∀ {m n o k₁ k₂} → N m → N k₁ → N k₂ →
                       n ≡ k₁ * succ₁ m →
                       o ≡ k₂ * succ₁ m →
                       n ∸ o ≡ (k₁ ∸ k₂) * succ₁ m
x∣y→x∣z→x∣y∸z-helper {m} {n} {o} {k₁} {k₂} Nm Nk₁ Nk₂ h₁ h₂ =
  n ∸ o                           ≡⟨ ∸-leftCong h₁ ⟩
  k₁ * succ₁ m ∸ o                ≡⟨ ∸-rightCong h₂ ⟩
  (k₁ * succ₁ m) ∸ (k₂ * succ₁ m) ≡⟨ sym (*∸-leftDistributive Nk₁ Nk₂ (nsucc Nm)) ⟩
  (k₁ ∸ k₂) * succ₁ m             ∎

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z nzero Nn No (0≢0 , _) m∣o = ⊥-elim (0≢0 refl)
x∣y→x∣z→x∣y∸z (nsucc {m} Nm) Nn No
              (_ , k₁ , Nk₁ , h₁)
              (_ , k₂ , Nk₂ , h₂) =
  (λ S≡0 → ⊥-elim (S≢0 S≡0))
  , k₁ ∸ k₂ , ∸-N Nk₁ Nk₂ , x∣y→x∣z→x∣y∸z-helper Nm Nk₁ Nk₂ h₁ h₂

-- If x divides y and z then x divides y + z.
x∣y→x∣z→x∣y+z-helper : ∀ {m n o k₁ k₂} → N m → N k₁ → N k₂ →
                       n ≡ k₁ * succ₁ m →
                       o ≡ k₂ * succ₁ m →
                       n + o ≡ (k₁ + k₂) * succ₁ m
x∣y→x∣z→x∣y+z-helper {m} {n} {o} {k₁} {k₂} Nm Nk₁ Nk₂ h₁ h₂ =
  n + o                           ≡⟨ +-leftCong h₁ ⟩
  k₁ * succ₁ m + o                ≡⟨ +-rightCong h₂ ⟩
  (k₁ * succ₁ m) + (k₂ * succ₁ m) ≡⟨ sym (*+-leftDistributive Nk₁ Nk₂ (nsucc Nm)) ⟩
  (k₁ + k₂) * succ₁ m             ∎

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z             nzero          Nn No (0≢0 , _) m∣o = ⊥-elim (0≢0 refl)
x∣y→x∣z→x∣y+z {n = n} {o} (nsucc {m} Nm) Nn No
              (_ , k₁ ,  Nk₁ , h₁)
              (_ , k₂ , Nk₂ , h₂) =
  (λ S≡0 → ⊥-elim (S≢0 S≡0))
  , k₁ + k₂ , +-N Nk₁ Nk₂ , x∣y→x∣z→x∣y+z-helper Nm Nk₁ Nk₂ h₁ h₂

-- If x divides y, and y is positive, then x ≤ y.
x∣S→x≤S : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → m ≤ succ₁ n
x∣S→x≤S  nzero          Nn (0≢0 , _)                  = ⊥-elim (0≢0 refl)
x∣S→x≤S  (nsucc {m} Nm) Nn (_ , .zero , nzero , Sn≡0*Sm) =
  ⊥-elim (0≢S (trans (sym (*-leftZero (succ₁ m))) (sym Sn≡0*Sm)))
x∣S→x≤S (nsucc {m} Nm) Nn (_ , .(succ₁ k) , nsucc {k} Nk , Sn≡Sk*Sm) =
  subst (λ t₁ → succ₁ m ≤ t₁)
        (sym Sn≡Sk*Sm)
        (subst (λ t₂ → succ₁ m ≤ t₂)
               (sym (*-Sx k (succ₁ m)))
               (x≤x+y (nsucc Nm) (*-N Nk (nsucc Nm))))
