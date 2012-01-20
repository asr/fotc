------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesATP where

open import Common.Function

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties
open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Divisibility.NotBy0
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
open import LTC-PCF.Data.Nat.PropertiesATP

------------------------------------------------------------------------------
-- Any positive number divides 0.
postulate S∣0 : ∀ {n} → N n →  succ₁ n ∣ zero
{-# ATP prove S∣0 *-0x #-}

-- The divisibility relation is reflexive for positive numbers.
-- For the proof using the ATP we added the helper hypothesis
-- N (succ₁ zero).
postulate ∣-refl-S-ah : ∀ {n} → N n → N (succ₁ zero) → succ₁ n ∣ succ₁ n
{-# ATP prove ∣-refl-S-ah *-leftIdentity #-}

∣-refl-S : ∀ {n} → N n → succ₁ n ∣ succ₁ n
∣-refl-S Nn = ∣-refl-S-ah Nn (sN zN)

-- If 'x' divides 'y' and 'z' then 'x' divides 'y ∸ z'.
postulate
  x∣y→x∣z→x∣y∸z-ah : ∀ {m n o k₁ k₂} → N m → N n → N k₁ → N k₂ →
                     n ≡ k₁ * succ₁ m →
                     o ≡ k₂ * succ₁ m →
                     n ∸ o ≡ (k₁ ∸ k₂) * succ₁ m
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove x∣y→x∣z→x∣y∸z-ah *∸-leftDistributive #-}

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z zN _ _ (0≠0 , _) m∣o = ⊥-elim $ 0≠0 refl
x∣y→x∣z→x∣y∸z (sN Nm) Nn No
              (0≠0 , k₁ , Nk₁ , n≡k₁Sm)
              (_   , k₂ , Nk₂ , o≡k₂Sm) =
  (λ S≡0 → ⊥-elim $ S≠0 S≡0) ,
  k₁ ∸ k₂ ,
  ∸-N Nk₁ Nk₂ ,
  x∣y→x∣z→x∣y∸z-ah Nm Nn Nk₁ Nk₂ n≡k₁Sm o≡k₂Sm

-- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
postulate
  x∣y→x∣z→x∣y+z-ah :  ∀ {m n o k₁ k₂} → N m → N n → N k₁ → N k₂ →
                      n ≡ k₁ * succ₁ m →
                      o ≡ k₂ * succ₁ m →
                      n + o ≡ (k₁ + k₂) * succ₁ m
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove x∣y→x∣z→x∣y+z-ah *+-leftDistributive #-}

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z zN      _  _ (0≠0 , _) m∣o = ⊥-elim $ 0≠0 refl
x∣y→x∣z→x∣y+z (sN Nm) Nn No
              (0≠0 , k₁ , Nk₁ , n≡k₁Sm)
              (_   , k₂ , Nk₂ , o≡k₂Sm) =
  (λ S≡0 → ⊥-elim $ S≠0 S≡0) ,
  k₁ + k₂ ,
  +-N Nk₁ Nk₂ ,
  x∣y→x∣z→x∣y+z-ah Nm Nn Nk₁ Nk₂ n≡k₁Sm o≡k₂Sm

-- If x divides y, and y is positive, then x ≤ y.
postulate x∣Sy→x≤Sy-helper₁ : ∀ {m n} → succ₁ n ≡ zero * succ₁ m → ⊥
{-# ATP prove x∣Sy→x≤Sy-helper₁ *-leftZero *-0x #-}

-- Nice proof by the ATP.
postulate
  x∣Sy→x≤Sy-helper₂ : ∀ {m n o} → N m → N n → N o →
                      succ₁ n ≡ succ₁ o * succ₁ m →
                      LE (succ₁ m) (succ₁ n)
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove x∣Sy→x≤Sy-helper₂ x≤x+y *-N *-Sx #-}

x∣Sy→x≤Sy : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → LE m (succ₁ n)
x∣Sy→x≤Sy  zN     Nn (0≠0 , _)                  = ⊥-elim $ 0≠0 refl
x∣Sy→x≤Sy (sN Nm) Nn (_ , .zero , zN , Sn≡0*Sm) =
  ⊥-elim $ x∣Sy→x≤Sy-helper₁ Sn≡0*Sm
x∣Sy→x≤Sy (sN {m} Nm) Nn (_ , .(succ₁ k) , sN {k} Nk , Sn≡Sk*Sm) =
  x∣Sy→x≤Sy-helper₂ Nm Nn Nk Sn≡Sk*Sm
