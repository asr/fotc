------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Data.Nat.Divisibility.By0.Properties where

open import Combined.FOTC.Base
open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Divisibility.By0
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.Inequalities.Properties
open import Combined.FOTC.Data.Nat.Properties

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
  x∣y→x∣z→x∣y∸z-helper : ∀ {m n o k k'} → N m → N k → N k' →
                         n ≡ k * m →
                         o ≡ k' * m →
                         n ∸ o ≡ (k ∸ k') * m
{-# ATP prove x∣y→x∣z→x∣y∸z-helper *∸-leftDistributive #-}

x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z Nm Nn No (k , Nk , h₁) (k' , Nk' , h₂) =
  k ∸ k' , ∸-N Nk Nk' , x∣y→x∣z→x∣y∸z-helper Nm Nk Nk' h₁ h₂

-- If x divides y and z then x divides y + z.
postulate
  x∣y→x∣z→x∣y+z-helper : ∀ {m n o k k'} → N m → N k → N k' →
                         n ≡ k * m →
                         o ≡ k' * m →
                         n + o ≡ (k + k') * m
{-# ATP prove x∣y→x∣z→x∣y+z-helper *+-leftDistributive #-}

x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z Nm Nn No (k , Nk , h₁) (k' , Nk' , h₂) =
  k + k' , +-N Nk Nk' , x∣y→x∣z→x∣y+z-helper Nm Nk Nk' h₁ h₂

-- If x divides y and y is positive, then x ≤ y.
postulate x∣S→x≤S-helper₁ : ∀ {m n} → succ₁ n ≡ zero * m → ⊥
{-# ATP prove x∣S→x≤S-helper₁ #-}

-- Nice proof by the ATPa.
postulate x∣S→x≤S-helper₂ : ∀ {m n o} → N m → N n → N o →
                            succ₁ n ≡ succ₁ o * m →
                            m ≤ succ₁ n
{-# ATP prove x∣S→x≤S-helper₂ x≤x+y *-N #-}

x∣S→x≤S : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → m ≤ succ₁ n
x∣S→x≤S Nm Nn (.zero , nzero , Sn≡0*m) = ⊥-elim (x∣S→x≤S-helper₁ Sn≡0*m)
x∣S→x≤S Nm Nn (.(succ₁ k) , nsucc {k} Nk , Sn≡Sk*m) =
  x∣S→x≤S-helper₂ Nm Nn Nk Sn≡Sk*m
