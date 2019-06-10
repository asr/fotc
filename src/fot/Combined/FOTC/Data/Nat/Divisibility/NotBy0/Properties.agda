------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Nat.Divisibility.NotBy0.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.Properties
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Divisibility.NotBy0
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.Inequalities.Properties
open import Combined.FOTC.Data.Nat.Properties

------------------------------------------------------------------------------
-- Any positive number divides 0.
postulate S∣0 : ∀ n → succ₁ n ∣ zero
{-# ATP prove S∣0 #-}

-- 0 doesn't divide any number.
postulate 0∤x : ∀ {n} → ¬ (zero ∣ n)
{-# ATP prove 0∤x #-}

-- The divisibility relation is reflexive for positive numbers.
--
-- For the proof using the ATPs we added the helper hypothesis
--
-- N (succ zero).
postulate ∣-refl-S-ah : ∀ {n} → N n → N (succ₁ zero) → succ₁ n ∣ succ₁ n
{-# ATP prove ∣-refl-S-ah *-leftIdentity #-}

∣-refl-S : ∀ {n} → N n → succ₁ n ∣ succ₁ n
∣-refl-S Nn = ∣-refl-S-ah Nn (nsucc nzero)

-- If x divides y and z then x divides y ∸ z.
postulate
  x∣y→x∣z→x∣y∸z-helper : ∀ {m n o k k'} → N m → N k → N k' →
                         n ≡ k * succ₁ m →
                         o ≡ k' * succ₁ m →
                         n ∸ o ≡ (k ∸ k') * succ₁ m
{-# ATP prove x∣y→x∣z→x∣y∸z-helper *∸-leftDistributive #-}

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z nzero _ _ (0≢0 , _) m∣o = ⊥-elim (0≢0 refl)
x∣y→x∣z→x∣y∸z (nsucc Nm) Nn No
              (_ , k , Nk , h₁)
              (_ , k' , Nk' , h₂) =
  (λ S≡0 → ⊥-elim (S≢0 S≡0))
  , k ∸ k' , ∸-N Nk Nk' , x∣y→x∣z→x∣y∸z-helper Nm Nk Nk' h₁ h₂

-- If x divides y and z then x divides y + z.
postulate
  x∣y→x∣z→x∣y+z-helper : ∀ {m n o k k'} → N m → N k → N k' →
                         n ≡ k * succ₁ m →
                         o ≡ k' * succ₁ m →
                         n + o ≡ (k + k') * succ₁ m
{-# ATP prove x∣y→x∣z→x∣y+z-helper *+-leftDistributive #-}

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z nzero      _  _ (0≢0 , _) m∣o = ⊥-elim (0≢0 refl)
x∣y→x∣z→x∣y+z (nsucc Nm) Nn No
              (_ , k , Nk , h₁)
              (_ , k' , Nk' , h₂) =
  (λ S≡0 → ⊥-elim (S≢0 S≡0))
  , k + k' , +-N Nk Nk' , x∣y→x∣z→x∣y+z-helper Nm Nk Nk' h₁ h₂

-- If x divides y and y is positive, then x ≤ y.
postulate x∣S→x≤S-ah₁ : ∀ {m n} → succ₁ n ≡ zero * succ₁ m → ⊥
{-# ATP prove x∣S→x≤S-ah₁ #-}

-- Nice proof by the Combined.
postulate x∣S→x≤S-ah₂ : ∀ {m n o} → N m → N n → N o →
                        succ₁ n ≡ succ₁ o * succ₁ m →
                        succ₁ m ≤ succ₁ n
{-# ATP prove x∣S→x≤S-ah₂ x≤x+y *-N #-}

x∣S→x≤S : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → m ≤ succ₁ n
x∣S→x≤S  nzero Nn (0≢0 , _) = ⊥-elim (0≢0 refl)
x∣S→x≤S (nsucc Nm) Nn (_ , .zero , nzero , Sn≡0*Sm) = ⊥-elim (x∣S→x≤S-ah₁ Sn≡0*Sm)
x∣S→x≤S (nsucc {m} Nm) Nn (_ , .(succ₁ k) , nsucc {k} Nk , Sn≡Sk*Sm) =
  x∣S→x≤S-ah₂ Nm Nn Nk Sn≡Sk*Sm
