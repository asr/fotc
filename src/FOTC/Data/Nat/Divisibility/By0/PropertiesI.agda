------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.By0.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning
open import Common.Function

open import FOTC.Base
open import FOTC.Base.Properties
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.By0
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI

------------------------------------------------------------------------------
-- The divisibility relation is reflexive.
∣-refl : ∀ {n} → N n → n ∣ n
∣-refl {n} Nn = succ₁ zero , (sN zN) , (sym (*-leftIdentity Nn))

-- If 'x' divides 'y' and 'z' then 'x' divides 'y - z'.
x∣y→x∣z→x∣y∸z-helper : ∀ {m n o k₁ k₂} → N m → N k₁ → N k₂ →
                       n ≡ k₁ * m →
                       o ≡ k₂ * m →
                       n ∸ o ≡ (k₁ ∸ k₂) * m
x∣y→x∣z→x∣y∸z-helper {m} {n} {o} {k₁} {k₂} Nm Nk₁ Nk₂ h₁ h₂ =
  n ∸ o               ≡⟨ subst (λ t → n ∸ o ≡ t ∸ o) h₁ refl ⟩
  k₁ * m ∸ o          ≡⟨ cong (_∸_ (k₁ * m)) h₂ ⟩
  (k₁ * m) ∸ (k₂ * m) ≡⟨ sym $ *∸-leftDistributive Nk₁ Nk₂ Nm ⟩
  (k₁ ∸ k₂) * m ∎

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z Nm Nn No (k₁ , Nk₁ , h₁) (k₂ , Nk₂ , h₂) =
  k₁ ∸ k₂ , ∸-N Nk₁ Nk₂ , x∣y→x∣z→x∣y∸z-helper Nm Nk₁ Nk₂ h₁ h₂

-- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
x∣y→x∣z→x∣y+z-helper : ∀ {m n o k₁ k₂} → N m → N k₁ → N k₂ →
                       n ≡ k₁ * m →
                       o ≡ k₂ * m →
                       n + o ≡ (k₁ + k₂) * m
x∣y→x∣z→x∣y+z-helper {m} {n} {o} {k₁} {k₂} Nm Nk₁ Nk₂ h₁ h₂ =
  n + o               ≡⟨ subst (λ t → n + o ≡ t + o) h₁ refl ⟩
  k₁ * m + o          ≡⟨ cong (_+_ (k₁ * m)) h₂ ⟩
  (k₁ * m) + (k₂ * m) ≡⟨ sym $ *+-leftDistributive Nk₁ Nk₂ Nm ⟩
  (k₁ + k₂) * m ∎

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z Nm Nn No (k₁ , Nk₁ , h₁) (k₂ , Nk₂ , h₂) =
  k₁ + k₂ , +-N Nk₁ Nk₂ , x∣y→x∣z→x∣y+z-helper Nm Nk₁ Nk₂ h₁ h₂

-- If x divides y, and y is positive, then x ≤ y.
x∣Sy→x≤Sy : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → LE m (succ₁ n)
x∣Sy→x≤Sy {m} Nm Nn (.zero , zN , Sn≡0*m) =
  ⊥-elim $ 0≢S $ trans (sym $ *-leftZero m) (sym Sn≡0*m)
x∣Sy→x≤Sy {m} Nm Nn (.(succ₁ k) , sN {k} Nk , Sn≡Sk*m) =
  subst (λ t₁ → LE m t₁)
        (sym Sn≡Sk*m)
        (subst (λ t₂ → LE m t₂)
               (sym $ *-Sx k m)
               (x≤x+y Nm (*-N Nk Nm)))

-- If 0 divides x, then x = 0.
0∣x→x≡0 : ∀ {m} → N m → zero ∣ m → m ≡ zero
0∣x→x≡0 zN          _                 = refl
0∣x→x≡0 (sN {m} Nm) (k , Nk , Sm≡k*0) =
  ⊥-elim (0≢S (trans (sym (*-leftZero k))
                     (trans (*-comm zN Nk) (sym Sm≡k*0))))
