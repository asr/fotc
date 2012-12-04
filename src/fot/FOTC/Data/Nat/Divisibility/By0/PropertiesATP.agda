------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.By0.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.By0
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP

------------------------------------------------------------------------------
-- Any positive number divides 0.
postulate S∣0 : ∀ n → succ₁ n ∣ zero
{-# ATP prove S∣0 #-}

-- 0 divides 0.
postulate 0∣0 : zero ∣ zero
{-# ATP prove 0∣0 #-}

-- The divisibility relation is reflexive.
postulate ∣-refl : ∀ {n} → N n → n ∣ n
{-# ATP prove ∣-refl *-leftIdentity #-}

-- If x divides y and z then x divides y ∸ z.
postulate
  x∣y→x∣z→x∣y∸z-helper : ∀ {m n o k₁ k₂} → N m → N k₁ → N k₂ →
                         n ≡ k₁ * m →
                         o ≡ k₂ * m →
                         n ∸ o ≡ (k₁ ∸ k₂) * m
{-# ATP prove x∣y→x∣z→x∣y∸z-helper *∸-leftDistributive #-}

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z Nm Nn No (k₁ , Nk₁ , h₁) (k₂ , Nk₂ , h₂) =
  k₁ ∸ k₂ , ∸-N Nk₁ Nk₂ , x∣y→x∣z→x∣y∸z-helper Nm Nk₁ Nk₂ h₁ h₂

-- If x divides y and z then x divides y + z.
postulate
  x∣y→x∣z→x∣y+z-helper : ∀ {m n o k₁ k₂} → N m → N k₁ → N k₂ →
                         n ≡ k₁ * m →
                         o ≡ k₂ * m →
                         n + o ≡ (k₁ + k₂) * m
{-# ATP prove x∣y→x∣z→x∣y+z-helper *+-leftDistributive #-}

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z Nm Nn No (k₁ , Nk₁ , h₁) (k₂ , Nk₂ , h₂) =
  k₁ + k₂ , +-N Nk₁ Nk₂ , x∣y→x∣z→x∣y+z-helper Nm Nk₁ Nk₂ h₁ h₂

-- If x divides y, and y is positive, then x ≤ y.
postulate x∣S→x≤S-helper₁ : ∀ {m n} → succ₁ n ≡ zero * m → ⊥
{-# ATP prove x∣S→x≤S-helper₁ #-}

-- Nice proof by the ATPa.
postulate
  x∣S→x≤S-helper₂ : ∀ {m n o} → N m → N n → N o →
                    succ₁ n ≡ succ₁ o * m →
                    m ≤ succ₁ n
{-# ATP prove x∣S→x≤S-helper₂ x≤x+y *-N #-}

x∣S→x≤S : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → m ≤ succ₁ n
x∣S→x≤S Nm Nn (.zero , nzero , Sn≡0*m) = ⊥-elim (x∣S→x≤S-helper₁ Sn≡0*m)
x∣S→x≤S Nm Nn (.(succ₁ k) , nsucc {k} Nk , Sn≡Sk*m) =
  x∣S→x≤S-helper₂ Nm Nn Nk Sn≡Sk*m
