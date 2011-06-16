------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module FOTC.Data.Nat.Divisibility.By0.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.Properties

open import Common.Function

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.By0
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP

------------------------------------------------------------------------------
-- The divisibility relation is reflexive.
postulate
  ∣-refl : ∀ {n} → N n → n ∣ n
{-# ATP prove ∣-refl *-leftIdentity #-}

-- If 'x' divides 'y' and 'z' then 'x' divides 'y ∸ z'.
postulate
  x∣y→x∣z→x∣y∸z-helper : ∀ {m n o k₁ k₂} → N m → N n → N k₁ → N k₂ →
                         n ≡ k₁ * m →
                         o ≡ k₂ * m →
                         n ∸ o ≡ (k₁ ∸ k₂) * m
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove x∣y→x∣z→x∣y∸z-helper *∸-leftDistributive #-}

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z Nm Nn No (k₁ , Nk₁ , n≡k₁m) (k₂ , Nk₂ , o≡k₂m) =
  k₁ ∸ k₂ ,
  ∸-N Nk₁ Nk₂ ,
  x∣y→x∣z→x∣y∸z-helper Nm Nn Nk₁ Nk₂ n≡k₁m o≡k₂m

-- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
postulate
  x∣y→x∣z→x∣y+z-helper : ∀ {m n o k₁ k₂} → N m → N n → N k₁ → N k₂ →
                         n ≡ k₁ * m →
                         o ≡ k₂ * m →
                         n + o ≡ (k₁ + k₂) * m
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove x∣y→x∣z→x∣y+z-helper *+-leftDistributive #-}

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z Nm Nn No (k₁ , Nk₁ , n≡k₁m) (k₂ , Nk₂ , o≡k₂m) =
  k₁ + k₂ ,
  +-N Nk₁ Nk₂ ,
  x∣y→x∣z→x∣y+z-helper Nm Nn Nk₁ Nk₂ n≡k₁m o≡k₂m

-- If x divides y, and y is positive, then x ≤ y.
postulate x∣Sy→x≤Sy-helper₁ : ∀ {m n} → succ n ≡ zero * m → ⊥
{-# ATP prove x∣Sy→x≤Sy-helper₁ #-}

-- Nice proof by the ATP.
postulate
  x∣Sy→x≤Sy-helper₂ : ∀ {m n o} → N m → N n → N o →
                      succ n ≡ succ o * m →
                      LE m (succ n)
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove x∣Sy→x≤Sy-helper₂ x≤x+y *-N #-}

x∣Sy→x≤Sy : ∀ {m n} → N m → N n → m ∣ (succ n) → LE m (succ n)
x∣Sy→x≤Sy Nm Nn (.zero     , zN        , Sn≡0*m) = ⊥-elim $ x∣Sy→x≤Sy-helper₁ Sn≡0*m
x∣Sy→x≤Sy Nm Nn (.(succ k) , sN {k} Nk , Sn≡Sk*m) =
  x∣Sy→x≤Sy-helper₂ Nm Nn Nk Sn≡Sk*m
