------------------------------------------------------------------------------
-- Properties of the divisibility relation (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Data.Nat.Divisibility.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER using ( subst )

open import LTC.Data.Nat
open import LTC.Data.Nat.Divisibility
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.PropertiesER
open import LTC.Data.Nat.PropertiesER
open import LTC.Relation.Equalities.Properties using ( ¬S≡0 )

open import MyStdLib.Function
import MyStdLib.Relation.Binary.EqReasoning
open module Divisibility-ER =
  MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : {n : D} → N n → succ n ∣ zero
S∣0 {n} Nn = (  ¬S≡0 ,
               ( zero , zN , sym (*-0x (succ n))))

-- 0 doesn't divide any number.
0∤x : {d : D} → ¬ (zero ∣ d)
0∤x ( 0≠0 , _ ) = ⊥-elim $ 0≠0 refl

-- The divisibility relation is reflexive for positive numbers.
∣-refl-S : {n : D} → N n → succ n ∣ succ n
∣-refl-S {n} Nn = ¬S≡0 , (succ zero) , sN zN , sym (*-leftIdentity (sN Nn))

-- If 'x' divides 'y' and 'z' then 'x' divides 'y - z'.
x∣y→x∣z→x∣y-z : {m n p : D} → N m → N n → N p → m ∣ n → m ∣ p → m ∣ n - p
x∣y→x∣z→x∣y-z             zN          Nn Np ( 0≠0 , _ ) m∣p = ⊥-elim (0≠0 refl)
x∣y→x∣z→x∣y-z {n = n} {p} (sN {m} Nm) Nn Np
              ( 0≠0 , ( k₁ , Nk₁ , n≡k₁Sm ))
              ( _   , ( k₂ , Nk₂ , p≡k₂Sm )) =
  (λ S≡0 → ⊥-elim (¬S≡0 S≡0)) , (k₁ - k₂) , minus-N Nk₁ Nk₂ , prf

  where
  prf : n - p ≡ (k₁ - k₂) * succ m
  prf =
    begin
      n - p                         ≡⟨ subst (λ t → n - p ≡ t - p)
                                             n≡k₁Sm
                                             refl
                                     ⟩
      k₁ * succ m - p               ≡⟨ subst (λ t → k₁ * succ m - p ≡
                                                    k₁ * succ m - t)
                                              p≡k₂Sm
                                              refl
                                     ⟩
      (k₁ * succ m) - (k₂ * succ m) ≡⟨ sym ([x-y]z≡xz*yz Nk₁ Nk₂ (sN Nm)) ⟩
      (k₁ - k₂) * succ m
    ∎

-- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
x∣y→x∣z→x∣y+z : {m n p : D} → N m → N n → N p → m ∣ n → m ∣ p → m ∣ n + p
x∣y→x∣z→x∣y+z             zN          Nn Np ( 0≠0 , _ ) m∣p = ⊥-elim (0≠0 refl)
x∣y→x∣z→x∣y+z {n = n} {p} (sN {m} Nm) Nn Np
              ( 0≠0 , ( k₁ , Nk₁ , n≡k₁Sm ))
              ( _   , ( k₂ , Nk₂ , p≡k₂Sm )) =
  (λ S≡0 → ⊥-elim (¬S≡0 S≡0)) , (k₁ + k₂) , +-N Nk₁ Nk₂ , prf

  where
  prf : n + p ≡ (k₁ + k₂) * succ m
  prf =
    begin
      n + p                         ≡⟨ subst (λ t → n + p ≡ t + p)
                                             n≡k₁Sm
                                             refl
                                     ⟩
      k₁ * succ m + p               ≡⟨ subst (λ t → k₁ * succ m + p ≡
                                                    k₁ * succ m + t)
                                              p≡k₂Sm
                                              refl
                                     ⟩
      (k₁ * succ m) + (k₂ * succ m) ≡⟨ sym ([x+y]z≡xz*yz Nk₁ Nk₂ (sN Nm)) ⟩
      (k₁ + k₂) * succ m
    ∎

-- If x divides y, and y is positive, then x ≤ y.
x∣S→x≤S : {m n : D} → N m → N n → m ∣ (succ n) → LE m (succ n)
x∣S→x≤S  zN     Nn  ( 0≠0 , _ )                      = ⊥-elim (0≠0 refl)
x∣S→x≤S (sN {m} Nm) Nn ( _ , .zero , zN , Sn≡0*Sm )  =
  ⊥-elim (0≠S (trans (sym (*-leftZero (succ m))) (sym Sn≡0*Sm)))
x∣S→x≤S (sN {m} Nm) Nn ( _ , .(succ k) , sN {k} Nk , Sn≡Sk*Sm ) =
  subst (λ t₁ → LE (succ m) t₁)
        (sym Sn≡Sk*Sm)
        (subst (λ t₂ → LE (succ m) t₂)
               (sym (*-Sx k (succ m)))
               (x≤x+y (sN Nm) (*-N Nk (sN Nm))))
