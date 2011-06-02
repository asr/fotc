------------------------------------------------------------------------------
-- Properties of the divisibility relation
------------------------------------------------------------------------------

module LTC-PCF.Data.Nat.Divisibility.PropertiesI where

open import LTC-PCF.Base
open import FOTC.Base.Properties using ( ¬S≡0 )

open import Common.Function using ( _$_ )

open import LTC-PCF.Data.Nat
  using ( _+_ ; _∸_ ; _*_
        ; N ; sN ; zN  -- The LTC natural numbers type.
        )
open import LTC-PCF.Data.Nat.Divisibility using ( _∣_ )
open import LTC-PCF.Data.Nat.Inequalities using ( LE )
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI
  using ( x≤x+y )
open import LTC-PCF.Data.Nat.PropertiesI
  using ( +-N ; ∸-N ; *-N
        ; *-0x ; *-Sx
        ; *-leftIdentity
        ; *-leftZero
        ; *+-leftDistributive
        ; *∸-leftDistributive
        )

open import LTC-PCF.Relation.Binary.EqReasoning

------------------------------------------------------------------------------
-- Any positive number divides 0.
S∣0 : ∀ {n} → N n → succ n ∣ zero
S∣0 {n} Nn = ¬S≡0 , zero , zN , sym (*-0x (succ n))

-- The divisibility relation is reflexive for positive numbers.
∣-refl-S : ∀ {n} → N n → succ n ∣ succ n
∣-refl-S {n} Nn = ¬S≡0 , succ zero , sN zN , sym (*-leftIdentity (sN Nn))

-- If 'x' divides 'y' and 'z' then 'x' divides 'y ∸ z'.
x∣y→x∣z→x∣y∸z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n ∸ o
x∣y→x∣z→x∣y∸z             zN          Nn No (0≠0 , _) m∣o = ⊥-elim $ 0≠0 refl
x∣y→x∣z→x∣y∸z {n = n} {o} (sN {m} Nm) Nn No
              (0≠0 , k₁ , Nk₁ , n≡k₁Sm)
              (_   , k₂ , Nk₂ , o≡k₂Sm) =
  (λ S≡0 → ⊥-elim $ ¬S≡0 S≡0) , k₁ ∸ k₂ , ∸-N Nk₁ Nk₂ , prf

  where
  prf : n ∸ o ≡ (k₁ ∸ k₂) * succ m
  prf =
    begin
      n ∸ o                         ≡⟨ subst (λ t → n ∸ o ≡ t ∸ o)
                                             n≡k₁Sm
                                             refl
                                    ⟩
      k₁ * succ m ∸ o               ≡⟨ subst (λ t → k₁ * succ m ∸ o ≡
                                                    k₁ * succ m ∸ t)
                                             o≡k₂Sm
                                             refl
                                    ⟩
      (k₁ * succ m) ∸ (k₂ * succ m) ≡⟨ sym $
                                       *∸-leftDistributive Nk₁ Nk₂ (sN Nm)
                                    ⟩
      (k₁ ∸ k₂) * succ m
    ∎

-- If 'x' divides 'y' and 'z' then 'x' divides 'y + z'.
x∣y→x∣z→x∣y+z : ∀ {m n o} → N m → N n → N o → m ∣ n → m ∣ o → m ∣ n + o
x∣y→x∣z→x∣y+z             zN          Nn No (0≠0 , _) m∣o = ⊥-elim $ 0≠0 refl
x∣y→x∣z→x∣y+z {n = n} {o} (sN {m} Nm) Nn No
              (0≠0 , k₁ , Nk₁ , n≡k₁Sm)
              (_   , k₂ , Nk₂ , o≡k₂Sm) =
  (λ S≡0 → ⊥-elim $ ¬S≡0 S≡0) , (k₁ + k₂) , +-N Nk₁ Nk₂ , prf

  where
  prf : n + o ≡ (k₁ + k₂) * succ m
  prf =
    begin
      n + o                         ≡⟨ subst (λ t → n + o ≡ t + o)
                                             n≡k₁Sm
                                             refl
                                    ⟩
      k₁ * succ m + o               ≡⟨ subst (λ t → k₁ * succ m + o ≡
                                                    k₁ * succ m + t)
                                             o≡k₂Sm
                                             refl
                                    ⟩
      (k₁ * succ m) + (k₂ * succ m) ≡⟨ sym $
                                       *+-leftDistributive Nk₁ Nk₂ (sN Nm)
                                    ⟩
      (k₁ + k₂) * succ m
    ∎

-- If x divides y, and y is positive, then x ≤ y.
x∣S→x≤S : ∀ {m n} → N m → N n → m ∣ (succ n) → LE m (succ n)
x∣S→x≤S  zN     Nn  (0≠0 , _)                     = ⊥-elim $ 0≠0 refl
x∣S→x≤S (sN {m} Nm) Nn (_ , .zero , zN , Sn≡0*Sm) =
  ⊥-elim $ 0≠S $ trans (sym $ *-leftZero (succ m)) (sym Sn≡0*Sm)
x∣S→x≤S (sN {m} Nm) Nn (_ , .(succ k) , sN {k} Nk , Sn≡Sk*Sm) =
  subst (λ t₁ → LE (succ m) t₁)
        (sym Sn≡Sk*Sm)
        (subst (λ t₂ → LE (succ m) t₂)
               (sym $ *-Sx k (succ m))
               (x≤x+y (sN Nm) (*-N Nk (sN Nm))))
