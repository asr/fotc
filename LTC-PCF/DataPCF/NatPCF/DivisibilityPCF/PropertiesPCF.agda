------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module LTC-PCF.DataPCF.NatPCF.DivisibilityPCF.PropertiesPCF where

open import LTC.Minimal

open import LTC-PCF.DataPCF.NatPCF
open import LTC-PCF.DataPCF.NatPCF.DivisibilityPCF
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF
open import LTC-PCF.DataPCF.NatPCF.InequalitiesPCF.PropertiesPCF
open import LTC-PCF.DataPCF.NatPCF.PropertiesPCF
open import LTC.Relation.Equalities.Properties using ( ¬S≡0 )

open import MyStdLib.Function

------------------------------------------------------------------------------
-- Any positive number divides 0.
postulate S∣0 : {n : D} → N n →  succ n ∣ zero
{-# ATP prove S∣0 zN *-0x #-}

-- The divisibility relation is reflexive for positive numbers.
-- For the proof using the ATP we added the auxiliar hypothesis
-- N (succ zero).
postulate ∣-refl-S-ah : {n : D} → N n → N (succ zero) → succ n ∣ succ n
{-# ATP prove ∣-refl-S-ah sN *-leftIdentity #-}

∣-refl-S : {n : D} → N n → succ n ∣ succ n
∣-refl-S Nn = ∣-refl-S-ah Nn (sN zN)

-- 0 doesn't divide any number.
0∤x : {d : D} → ¬ (zero ∣ d)
0∤x ( 0≠0 , _ ) = ⊥-elim $ 0≠0 refl

-- If 'x' divides 'y' and 'z' then 'x' divides 'y - z'.
postulate
  x∣y→x∣z→x∣y-z-ah : {m n p k₁ k₂ : D} → N m → N n → N k₁ → N k₂ →
                      n ≡ k₁ * succ m →
                      p ≡ k₂ * succ m →
                      n - p ≡ (k₁ - k₂) * succ m
{-# ATP prove x∣y→x∣z→x∣y-z-ah [x-y]z≡xz*yz sN #-}

x∣y→x∣z→x∣y-z : {m n p : D} → N m → N n → N p → m ∣ n → m ∣ p → m ∣ n - p
x∣y→x∣z→x∣y-z zN _ _ ( 0≠0 , _ ) m∣p = ⊥-elim (0≠0 refl)
x∣y→x∣z→x∣y-z (sN Nm) Nn Np
              ( 0≠0 , ( k₁ , Nk₁ , n≡k₁Sm ))
              ( _   , ( k₂ , Nk₂ , p≡k₂Sm )) =
  (λ S≡0 → ⊥-elim (¬S≡0 S≡0)) ,
  (k₁ - k₂) ,
  minus-N Nk₁ Nk₂ ,
  x∣y→x∣z→x∣y-z-ah Nm Nn Nk₁ Nk₂ n≡k₁Sm p≡k₂Sm

-- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
postulate
  x∣y→x∣z→x∣y+z-ah : {m n p k₁ k₂ : D} → N m → N n → N k₁ → N k₂ →
                      n ≡ k₁ * succ m →
                      p ≡ k₂ * succ m →
                      n + p ≡ (k₁ + k₂) * succ m
{-# ATP prove x∣y→x∣z→x∣y+z-ah [x+y]z≡xz*yz sN #-}

x∣y→x∣z→x∣y+z : {m n p : D} → N m → N n → N p → m ∣ n → m ∣ p → m ∣ n + p
x∣y→x∣z→x∣y+z zN      _  _ ( 0≠0 , _ ) m∣p = ⊥-elim (0≠0 refl)
x∣y→x∣z→x∣y+z (sN Nm) Nn Np
              ( 0≠0 , ( k₁ , Nk₁ , n≡k₁Sm ))
              ( _   , ( k₂ , Nk₂ , p≡k₂Sm )) =
  (λ S≡0 → ⊥-elim (¬S≡0 S≡0)) ,
  (k₁ + k₂) ,
  +-N Nk₁ Nk₂ ,
  x∣y→x∣z→x∣y+z-ah Nm Nn Nk₁ Nk₂ n≡k₁Sm p≡k₂Sm

-- If x divides y, and y is positive, then x ≤ y.
postulate
  x∣S→x≤S-ah₁ : {m n : D} → succ n ≡ zero * succ m → ⊥
{-# ATP prove x∣S→x≤S-ah₁ *-leftZero *-0x sN #-}

-- Nice proof by the ATP.
postulate
  x∣S→x≤S-ah₂ : {m n k : D} → N m → N n → N k →
                succ n ≡ succ k * succ m →
                LE (succ m) (succ n)
{-# ATP prove x∣S→x≤S-ah₂ x≤x+y *-N sN *-Sx #-}

x∣S→x≤S : {m n : D} → N m → N n → m ∣ (succ n) → LE m (succ n)
x∣S→x≤S  zN     Nn ( 0≠0 , _ )                   = ⊥-elim (0≠0 refl)
x∣S→x≤S (sN Nm) Nn ( _ , .zero , zN , Sn≡0*Sm )  = ⊥-elim (x∣S→x≤S-ah₁ Sn≡0*Sm)
x∣S→x≤S (sN {m} Nm) Nn ( _ , .(succ k) , sN {k} Nk , Sn≡Sk*Sm ) =
  x∣S→x≤S-ah₂ Nm Nn Nk Sn≡Sk*Sm
