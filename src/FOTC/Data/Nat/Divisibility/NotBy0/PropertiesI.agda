------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI where

open import Common.Function

open import FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.Properties
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Divisibility.NotBy0
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI

------------------------------------------------------------------------------
-- The divisibility relation is reflexive for positive numbers.
∣-refl-S : ∀ {n} → N n → succ₁ n ∣ succ₁ n
∣-refl-S {n} Nn = S≠0 , succ₁ zero ,, sN zN , sym (*-leftIdentity (sN Nn))

-- If 'x' divides 'y' and 'z' then 'x' divides 'y - z'.
x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z             zN          Nn No (0≠0 , _) m∣o = ⊥-elim $ 0≠0 refl
x∣y→x∣z→x∣y∸z {n = n} {o} (sN {m} Nm) Nn No
              (0≠0 , k₁ ,, Nk₁ , n≡k₁Sm)
              (_   , k₂ ,, Nk₂ , o≡k₂Sm) =
  (λ S≡0 → ⊥-elim $ S≠0 S≡0) , k₁ ∸ k₂ ,, ∸-N Nk₁ Nk₂ , prf

  where
  prf : n ∸ o ≡ (k₁ ∸ k₂) * succ₁ m
  prf =
    n ∸ o
      ≡⟨ subst (λ t → n ∸ o ≡ t ∸ o) n≡k₁Sm refl ⟩
    k₁ * succ₁ m ∸ o
       ≡⟨ cong (_∸_ (k₁ * succ₁ m)) o≡k₂Sm ⟩
    (k₁ * succ₁ m) ∸ (k₂ * succ₁ m)
      ≡⟨ sym $ *∸-leftDistributive Nk₁ Nk₂ (sN Nm) ⟩
    (k₁ ∸ k₂) * succ₁ m ∎

-- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z             zN          Nn No (0≠0 , _) m∣o = ⊥-elim $ 0≠0 refl
x∣y→x∣z→x∣y+z {n = n} {o} (sN {m} Nm) Nn No
              (0≠0 , k₁ ,, Nk₁ , n≡k₁Sm)
              (_   , k₂ ,, Nk₂ , o≡k₂Sm) =
  (λ S≡0 → ⊥-elim $ S≠0 S≡0) , k₁ + k₂ ,, +-N Nk₁ Nk₂ , prf

  where
  prf : n + o ≡ (k₁ + k₂) * succ₁ m
  prf =
    n + o
      ≡⟨ subst (λ t → n + o ≡ t + o) n≡k₁Sm refl ⟩
    k₁ * succ₁ m + o
       ≡⟨ cong (_+_ (k₁ * succ₁ m)) o≡k₂Sm ⟩
    (k₁ * succ₁ m) + (k₂ * succ₁ m)
      ≡⟨ sym $ *+-leftDistributive Nk₁ Nk₂ (sN Nm) ⟩
    (k₁ + k₂) * succ₁ m ∎

-- If x divides y, and y is positive, then x ≤ y.
x∣S→x≤S : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → LE m (succ₁ n)
x∣S→x≤S  zN     Nn  (0≠0 , _)                     = ⊥-elim $ 0≠0 refl
x∣S→x≤S (sN {m} Nm) Nn (_ , .zero ,, zN , Sn≡0*Sm) =
  ⊥-elim $ 0≠S $ trans (sym $ *-leftZero (succ₁ m)) (sym Sn≡0*Sm)
x∣S→x≤S (sN {m} Nm) Nn (_ , .(succ₁ k) ,, sN {k} Nk , Sn≡Sk*Sm) =
  subst (λ t₁ → LE (succ₁ m) t₁)
        (sym Sn≡Sk*Sm)
        (subst (λ t₂ → LE (succ₁ m) t₂)
               (sym $ *-Sx k (succ₁ m))
               (x≤x+y (sN Nm) (*-N Nk (sN Nm))))
