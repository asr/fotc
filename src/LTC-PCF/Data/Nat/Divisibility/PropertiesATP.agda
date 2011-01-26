------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Divisibility.PropertiesATP where

open import LTC.Base
open import LTC.Base.Properties using ( ¬S≡0 )

open import Common.Function using ( _$_ )

open import LTC-PCF.Data.Nat
  using ( _+_ ; _∸_ ; _*_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Divisibility using ( _∣_ )
open import LTC-PCF.Data.Nat.Inequalities using ( LE )
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
  using ( x≤x+y )
open import LTC-PCF.Data.Nat.PropertiesATP
  using ( +-N ; ∸-N ; *-N
        ; *-0x ; *-Sx
        ; *-leftIdentity
        ; *-leftZero
        ; *+-leftDistributive
        ; *∸-leftDistributive
        )

------------------------------------------------------------------------------
-- Any positive number divides 0.
postulate S∣0 : ∀ {n} → N n →  succ n ∣ zero
{-# ATP prove S∣0 zN *-0x #-}

-- The divisibility relation is reflexive for positive numbers.
-- For the proof using the ATP we added the auxiliary hypothesis
-- N (succ zero).
postulate ∣-refl-S-ah : ∀ {n} → N n → N (succ zero) → succ n ∣ succ n
{-# ATP prove ∣-refl-S-ah sN *-leftIdentity #-}

∣-refl-S : ∀ {n} → N n → succ n ∣ succ n
∣-refl-S Nn = ∣-refl-S-ah Nn (sN zN)

-- If 'x' divides 'y' and 'z' then 'x' divides 'y ∸ z'.
postulate
  x∣y→x∣z→x∣y∸z-ah : ∀ {m n o k₁ k₂} → N m → N n → N k₁ → N k₂ →
                     n ≡ k₁ * succ m →
                     o ≡ k₂ * succ m →
                     n ∸ o ≡ (k₁ ∸ k₂) * succ m
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove x∣y→x∣z→x∣y∸z-ah *∸-leftDistributive sN #-}

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z zN _ _ (0≠0 , _) m∣o = ⊥-elim $ 0≠0 refl
x∣y→x∣z→x∣y∸z (sN Nm) Nn No
              (0≠0 , k₁ , Nk₁ , n≡k₁Sm)
              (_   , k₂ , Nk₂ , o≡k₂Sm) =
  (λ S≡0 → ⊥-elim $ ¬S≡0 S≡0) ,
  k₁ ∸ k₂ ,
  ∸-N Nk₁ Nk₂ ,
  x∣y→x∣z→x∣y∸z-ah Nm Nn Nk₁ Nk₂ n≡k₁Sm o≡k₂Sm

-- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
postulate
  x∣y→x∣z→x∣y+z-ah :  ∀ {m n o k₁ k₂} → N m → N n → N k₁ → N k₂ →
                      n ≡ k₁ * succ m →
                      o ≡ k₂ * succ m →
                      n + o ≡ (k₁ + k₂) * succ m
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove x∣y→x∣z→x∣y+z-ah *+-leftDistributive sN #-}

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z zN      _  _ (0≠0 , _) m∣o = ⊥-elim $ 0≠0 refl
x∣y→x∣z→x∣y+z (sN Nm) Nn No
              (0≠0 , k₁ , Nk₁ , n≡k₁Sm)
              (_   , k₂ , Nk₂ , o≡k₂Sm) =
  (λ S≡0 → ⊥-elim $ ¬S≡0 S≡0) ,
  k₁ + k₂ ,
  +-N Nk₁ Nk₂ ,
  x∣y→x∣z→x∣y+z-ah Nm Nn Nk₁ Nk₂ n≡k₁Sm o≡k₂Sm

-- If x divides y, and y is positive, then x ≤ y.
postulate
  x∣S→x≤S-ah₁ : ∀ {m n} → succ n ≡ zero * succ m → ⊥
{-# ATP prove x∣S→x≤S-ah₁ *-leftZero *-0x sN #-}

-- Nice proof by the ATP.
postulate
  x∣S→x≤S-ah₂ : ∀ {m n o} → N m → N n → N o →
                succ n ≡ succ o * succ m →
                LE (succ m) (succ n)
-- Metis 2.3 (release 20101019): SZS status Unknown (using timeout 180 sec).
{-# ATP prove x∣S→x≤S-ah₂ x≤x+y *-N sN *-Sx #-}

x∣S→x≤S : ∀ {m n} → N m → N n → m ∣ (succ n) → LE m (succ n)
x∣S→x≤S  zN     Nn (0≠0 , _)                  = ⊥-elim $ 0≠0 refl
x∣S→x≤S (sN Nm) Nn (_ , .zero , zN , Sn≡0*Sm) = ⊥-elim $ x∣S→x≤S-ah₁ Sn≡0*Sm
x∣S→x≤S (sN {m} Nm) Nn (_ , .(succ k) , sN {k} Nk , Sn≡Sk*Sm) =
  x∣S→x≤S-ah₂ Nm Nn Nk Sn≡Sk*Sm
