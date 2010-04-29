------------------------------------------------------------------------------
-- Properties of the divisibility relation (using equational reasoning)
------------------------------------------------------------------------------

module LTC.Relation.Divisibility.PropertiesER where

open import LTC.Minimal
open import LTC.MinimalER

open import LTC.Data.N
open import LTC.Function.Arithmetic
open import LTC.Function.Arithmetic.Properties using ( *-leftIdentity )
open import LTC.Function.Arithmetic.PropertiesER
open import LTC.Relation.Divisibility
open import LTC.Relation.Equalities.PropertiesER

open import MyStdLib.Function
import MyStdLib.Relation.Binary.EqReasoning
open module DPER = MyStdLib.Relation.Binary.EqReasoning.StdLib _≡_ refl trans

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
x∣y→x∣z→x∣y-z zN Nn Np ( 0≠0 , _) m∣p = ⊥-elim (0≠0 refl)
x∣y→x∣z→x∣y-z .{succ m} {n} {p} (sN {m} Nm) Nn Np
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
