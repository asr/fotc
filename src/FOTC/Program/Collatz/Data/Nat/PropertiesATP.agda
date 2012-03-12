------------------------------------------------------------------------------
-- Arithmetic properties (added for the Collatz function example)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Collatz.Data.Nat.PropertiesATP where

open import FOTC.Base
open import FOTC.Base.PropertiesATP
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------

^-N : ∀ {m n} → N m → N n → N (m ^ n)
^-N {m} Nm zN          = subst N (sym (^-0 m)) (sN zN)
^-N {m} Nm (sN {n} Nn) = subst N (sym (^-S m n)) (*-N Nm (^-N Nm Nn))

postulate 2*SSx≥2 : ∀ {n} → N n → GE (two * succ₁ (succ₁ n)) two
{-# ATP prove 2*SSx≥2 #-}

2x/2≡x : ∀ {n} → N n → two * n / two ≡ n
2x/2≡x zN = prf
  where
  postulate prf : two * zero / two ≡ zero
  {-# ATP prove prf *-rightZero #-}

2x/2≡x (sN zN) = prf
  where
  postulate prf : two * succ₁ zero / two ≡ succ₁ zero
  {-# ATP prove prf *-rightIdentity x≥x x∸x≡0 #-}

2x/2≡x (sN (sN {n} Nn)) = prf (2x/2≡x (sN Nn))
  where
  postulate prf : two * succ₁ n / two ≡ succ₁ n →  -- IH.
                  two * succ₁ (succ₁ n) / two ≡ succ₁ (succ₁ n)
  {-# ATP prove prf 2*SSx≥2 *-leftZero +-rightIdentity +-comm +-N #-}

postulate 2^[x+1]/2≡2^x : ∀ {n} → N n → (two ^ (succ₁ n)) / two ≡ two ^ n
{-# ATP prove 2^[x+1]/2≡2^x 2x/2≡x ^-N #-}

Sx≡2^0→x≡0 : ∀ {n} → N n → succ₁ n ≡ two ^ zero → n ≡ zero
Sx≡2^0→x≡0 zN         _       = refl
Sx≡2^0→x≡0(sN {n} Nn) SSn≡2^0 = ⊥-elim prf
  where
  postulate prf : ⊥
  {-# ATP prove prf #-}

+∸2 : ∀ {n} → N n → ¬ (n ≡ zero) → ¬ (n ≡ one) → n ≡ succ₁ (succ₁ (n ∸ two))
+∸2 zN               n≢0 n≢1 = ⊥-elim (n≢0 refl)
+∸2 (sN zN)          n≢0 n≢1 = ⊥-elim (n≢1 refl)
+∸2 (sN (sN {n} Nn)) n≢0 n≢1 = prf
  where
  -- See the interactive proof.
  postulate prf : succ₁ (succ₁ n) ≡ succ₁ (succ₁ (succ₁ (succ₁ n) ∸ two))

2^x≢0 : ∀ {n} → N n → ¬ (two ^ n ≡ zero)
2^x≢0 zN          h = ⊥-elim (0≢S (trans (sym h) (^-0 two)))
2^x≢0 (sN {n} Nn) h = prf (2^x≢0 Nn)
  where
  postulate prf : ¬ (two ^ n ≡ zero) →  -- IH.
                  ⊥
  {-# ATP prove prf xy≡0→x≡0∨y≡0 ^-N #-}

-- ToDo.
postulate 2^[x+1]≢1 : ∀ {n} → N n → ¬ (two ^ (succ₁ n) ≡ one)

Sx-Even→x-Odd : ∀ {n} → N n → Even (succ₁ n) → Odd n
Sx-Even→x-Odd zN          h = ⊥-elim prf
  where
  postulate prf : ⊥
  {-# ATP prove prf #-}

Sx-Even→x-Odd (sN {n} Nn) h = trans (sym (even-S (succ₁ n))) h

Sx-Odd→x-Even : ∀ {n} → N n → Odd (succ₁ n) → Even n
Sx-Odd→x-Even zN          _ = even-0
Sx-Odd→x-Even (sN {n} Nn) h = trans (sym (odd-S (succ₁ n))) h

mutual
  ∸-Even : ∀ {m n} → N m → N n → Even m → Even n → Even (m ∸ n)
  ∸-Even {m} Nm zN                   h₁ _ = subst Even (sym (∸-x0 m)) h₁
  ∸-Even     zN          (sN {n} Nn) h₁ _ = subst Even (sym (∸-0S n)) h₁
  ∸-Even     (sN {m} Nm) (sN {n} Nn) h₁ h₂ = prf
    where
    postulate prf : Even (succ₁ m ∸ succ₁ n)
    {-# ATP prove prf ∸-Odd Sx-Even→x-Odd #-}

  ∸-Odd : ∀ {m n} → N m → N n → Odd m → Odd n → Even (m ∸ n)
  ∸-Odd zN          Nn          h₁ _  = ⊥-elim (true≢false (trans (sym h₁) odd-0))
  ∸-Odd (sN Nm)     zN          _  h₂ = ⊥-elim (true≢false (trans (sym h₂) odd-0))
  ∸-Odd (sN {m} Nm) (sN {n} Nn) h₁ h₂ = prf
    where
    postulate prf : Even (succ₁ m ∸ succ₁ n)
    {-# ATP prove prf ∸-Even Sx-Odd→x-Even #-}

x-Even→SSx-Even : ∀ {n} → N n → Even n → Even (succ₁ (succ₁ n))
x-Even→SSx-Even zN h = prf
  where
  postulate prf : Even (succ₁ (succ₁ zero))
  {-# ATP prove prf #-}

x-Even→SSx-Even (sN {n} Nn) h = prf
  where
  postulate prf : Even (succ₁ (succ₁ (succ₁ n)))
  {-# ATP prove prf #-}

x+x-Even : ∀ {n} → N n → Even (n + n)
x+x-Even zN          = subst Even (sym (+-rightIdentity zN)) even-0
x+x-Even (sN {n} Nn) = prf (x+x-Even Nn)
  where
  postulate prf : Even (n + n) →  -- IH.
                  Even (succ₁ n + succ₁ n)
  {-# ATP prove prf x-Even→SSx-Even +-N +-comm #-}

2x-Even : ∀ {n} → N n → Even (two * n)
2x-Even zN          = subst Even (sym (*-rightZero 2-N)) even-0
2x-Even (sN {n} Nn) = prf
  where
  postulate prf : Even (two * succ₁ n)
  {-# ATP prove prf x-Even→SSx-Even x+x-Even +-N +-comm +-rightIdentity #-}
