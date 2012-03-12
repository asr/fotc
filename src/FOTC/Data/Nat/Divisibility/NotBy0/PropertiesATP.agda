------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.NotBy0.PropertiesATP where

open import Common.Function

open import FOTC.Base
open import FOTC.Base.Properties
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.NotBy0
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP

------------------------------------------------------------------------------
-- The divisibility relation is reflexive for positive numbers.
-- For the proof using the ATP we added the helper hypothesis
-- N (succ zero).
postulate ∣-refl-S-ah : ∀ {n} → N n → N (succ₁ zero) → succ₁ n ∣ succ₁ n
{-# ATP prove ∣-refl-S-ah *-leftIdentity #-}

∣-refl-S : ∀ {n} → N n → succ₁ n ∣ succ₁ n
∣-refl-S Nn = ∣-refl-S-ah Nn (sN zN)

-- If 'x' divides 'y' and 'z' then 'x' divides 'y ∸ z'.
postulate
  x∣y→x∣z→x∣y∸z-helper : ∀ {m n o k₁ k₂} → N m → N k₁ → N k₂ →
                         n ≡ k₁ * succ₁ m →
                         o ≡ k₂ * succ₁ m →
                         n ∸ o ≡ (k₁ ∸ k₂) * succ₁ m
{-# ATP prove x∣y→x∣z→x∣y∸z-helper *∸-leftDistributive #-}

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z zN _ _ (0≢0 , _) m∣o = ⊥-elim $ 0≢0 refl
x∣y→x∣z→x∣y∸z (sN Nm) Nn No
              (_ , k₁ , Nk₁ , h₁)
              (_ , k₂ , Nk₂ , h₂) =
  (λ S≡0 → ⊥-elim $ S≢0 S≡0)
  , k₁ ∸ k₂ , ∸-N Nk₁ Nk₂ , x∣y→x∣z→x∣y∸z-helper Nm Nk₁ Nk₂ h₁ h₂

-- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
postulate
  x∣y→x∣z→x∣y+z-helper : ∀ {m n o k₁ k₂} → N m → N k₁ → N k₂ →
                         n ≡ k₁ * succ₁ m →
                         o ≡ k₂ * succ₁ m →
                         n + o ≡ (k₁ + k₂) * succ₁ m
{-# ATP prove x∣y→x∣z→x∣y+z-helper *+-leftDistributive #-}

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z zN      _  _ (0≢0 , _) m∣o = ⊥-elim $ 0≢0 refl
x∣y→x∣z→x∣y+z (sN Nm) Nn No
              (_ , k₁ , Nk₁ , h₁)
              (_ , k₂ , Nk₂ , h₂) =
  (λ S≡0 → ⊥-elim $ S≢0 S≡0)
  , k₁ + k₂ , +-N Nk₁ Nk₂ , x∣y→x∣z→x∣y+z-helper Nm Nk₁ Nk₂ h₁ h₂

-- If x divides y, and y is positive, then x ≤ y.
postulate x∣S→x≤S-ah₁ : ∀ {m n} → succ₁ n ≡ zero * succ₁ m → ⊥
{-# ATP prove x∣S→x≤S-ah₁ #-}

-- Nice proof by the ATP.
postulate
  x∣S→x≤S-ah₂ : ∀ {m n o} → N m → N n → N o →
                succ₁ n ≡ succ₁ o * succ₁ m →
                LE (succ₁ m) (succ₁ n)
{-# ATP prove x∣S→x≤S-ah₂ x≤x+y *-N #-}

x∣S→x≤S : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → LE m (succ₁ n)
x∣S→x≤S  zN Nn (0≢0 , _) = ⊥-elim $ 0≢0 refl
x∣S→x≤S (sN Nm) Nn (_ , .zero , zN , Sn≡0*Sm) = ⊥-elim $ x∣S→x≤S-ah₁ Sn≡0*Sm
x∣S→x≤S (sN {m} Nm) Nn (_ , .(succ₁ k) , sN {k} Nk , Sn≡Sk*Sm) =
  x∣S→x≤S-ah₂ Nm Nn Nk Sn≡Sk*Sm
