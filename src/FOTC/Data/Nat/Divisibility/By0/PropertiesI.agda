------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Nat.Divisibility.By0.PropertiesI where

open import Common.Function

open import FOL.Relation.Binary.EqReasoning

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
∣-refl {n} Nn = ∃-intro ((sN zN) , (sym (*-leftIdentity Nn)))

-- If 'x' divides 'y' and 'z' then 'x' divides 'y - z'.
-- 2012-02-28. We required the existential witness on a pattern matching.
x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z {m} {n} {o} Nm Nn No
              (∃-intro {k₁} (Nk₁ , n≡k₁m))
              (∃-intro {k₂} (Nk₂ , o≡k₂m)) = ∃-intro (∸-N Nk₁ Nk₂ , prf)

  where
  prf : n ∸ o ≡ (k₁ ∸ k₂) * m
  prf =
    n ∸ o               ≡⟨ subst (λ t → n ∸ o ≡ t ∸ o) n≡k₁m refl ⟩
    k₁ * m ∸ o          ≡⟨ cong (_∸_ (k₁ * m)) o≡k₂m ⟩
    (k₁ * m) ∸ (k₂ * m) ≡⟨ sym $ *∸-leftDistributive Nk₁ Nk₂ Nm ⟩
    (k₁ ∸ k₂) * m ∎

-- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
-- 2012-02-28. We required the existential witness on a pattern matching.
x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z {m} {n} {o} Nm Nn No
              (∃-intro {k₁} (Nk₁ , n≡k₁m))
              (∃-intro {k₂} (Nk₂ , o≡k₂m)) = ∃-intro (+-N Nk₁ Nk₂ , prf)
  where
  prf : n + o ≡ (k₁ + k₂) * m
  prf =
    n + o               ≡⟨ subst (λ t → n + o ≡ t + o) n≡k₁m refl ⟩
    k₁ * m + o          ≡⟨ cong (_+_ (k₁ * m)) o≡k₂m ⟩
    (k₁ * m) + (k₂ * m) ≡⟨ sym $ *+-leftDistributive Nk₁ Nk₂ Nm ⟩
    (k₁ + k₂) * m ∎

-- If x divides y, and y is positive, then x ≤ y.
x∣Sy→x≤Sy : ∀ {m n} → N m → N n → m ∣ (succ₁ n) → LE m (succ₁ n)
x∣Sy→x≤Sy {m} Nm Nn (∃-intro (zN , Sn≡0*m)) =
  ⊥-elim $ 0≠S $ trans (sym $ *-leftZero m) (sym Sn≡0*m)
x∣Sy→x≤Sy {m} Nm Nn (∃-intro (sN {k} Nk , Sn≡Sk*m)) =
  subst (λ t₁ → LE m t₁)
        (sym Sn≡Sk*m)
        (subst (λ t₂ → LE m t₂)
               (sym $ *-Sx k m)
               (x≤x+y Nm (*-N Nk Nm)))

-- If 0 divides x, the x = 0.
-- 2012-02-28. We required the existential witness on a pattern matching.
0∣x→x≡0 : ∀ {m} → N m → zero ∣ m → m ≡ zero
0∣x→x≡0 zN          _                    = refl
0∣x→x≡0 (sN {m} Nm) (∃-intro {k} (Nk , Sm≡k*zero)) =
  ⊥-elim (0≠S (trans (sym (*-leftZero k)) (sym prf)))
  where
  prf : succ₁ m ≡ zero * k
  prf = succ₁ m   ≡⟨ Sm≡k*zero ⟩
        k * zero  ≡⟨ *-comm Nk zN ⟩
        zero * k ∎
