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
^-N {m} Nm nzero          = subst N (sym (^-0 m)) (nsucc nzero)
^-N {m} Nm (nsucc {n} Nn) = subst N (sym (^-S m n)) (*-N Nm (^-N Nm Nn))

postulate 2*SSx≥2 : ∀ {n} → N n → GE (two * succ₁ (succ₁ n)) two
{-# ATP prove 2*SSx≥2 #-}

2x/2≡x : ∀ {n} → N n → two * n / two ≡ n
2x/2≡x nzero = prf
  where postulate prf : two * zero / two ≡ zero
        {-# ATP prove prf *-rightZero #-}
2x/2≡x (nsucc nzero) = prf
  where postulate prf : two * succ₁ zero / two ≡ succ₁ zero
        {-# ATP prove prf *-rightIdentity x≥x x∸x≡0 #-}
2x/2≡x (nsucc (nsucc {n} Nn)) = prf (2x/2≡x (nsucc Nn))
  where postulate prf : two * succ₁ n / two ≡ succ₁ n →
                        two * succ₁ (succ₁ n) / two ≡ succ₁ (succ₁ n)
        {-# ATP prove prf 2*SSx≥2 +-rightIdentity +-comm +-N #-}

postulate 2^[x+1]/2≡2^x : ∀ {n} → N n → (two ^ (succ₁ n)) / two ≡ two ^ n
{-# ATP prove 2^[x+1]/2≡2^x 2x/2≡x ^-N #-}

Sx≡2^0→x≡0 : ∀ {n} → N n → succ₁ n ≡ two ^ zero → n ≡ zero
Sx≡2^0→x≡0 nzero         _       = refl
Sx≡2^0→x≡0(nsucc {n} Nn) SSn≡2^0 = ⊥-elim prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}

+∸2 : ∀ {n} → N n → n ≢ zero → n ≢ one → n ≡ succ₁ (succ₁ (n ∸ two))
+∸2 nzero                  n≢0 n≢1 = ⊥-elim (n≢0 refl)
+∸2 (nsucc nzero)          n≢0 n≢1 = ⊥-elim (n≢1 refl)
+∸2 (nsucc (nsucc {n} Nn)) n≢0 n≢1 = prf
  where
  -- See the interactive proof.
  postulate prf : succ₁ (succ₁ n) ≡ succ₁ (succ₁ (succ₁ (succ₁ n) ∸ two))

2^x≢0 : ∀ {n} → N n → two ^ n ≢ zero
2^x≢0 nzero          h = ⊥-elim (0≢S (trans (sym h) (^-0 two)))
2^x≢0 (nsucc {n} Nn) h = prf (2^x≢0 Nn)
  where postulate prf : two ^ n ≢ zero →  ⊥
        {-# ATP prove prf xy≡0→x≡0∨y≡0 ^-N #-}

2^[x+1]≢1 : ∀ {n} → N n → two ^ (succ₁ n) ≢ one
2^[x+1]≢1 {n} Nn h =
  Sx≢x (nsucc nzero) (xy≡1→x≡1 2-N (^-N 2-N Nn) (trans (sym (^-S two n)) h))

Sx-Even→x-Odd : ∀ {n} → N n → Even (succ₁ n) → Odd n
Sx-Even→x-Odd nzero  h = ⊥-elim prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}
Sx-Even→x-Odd (nsucc {n} Nn) h = trans (sym (even-S (succ₁ n))) h

Sx-Odd→x-Even : ∀ {n} → N n → Odd (succ₁ n) → Even n
Sx-Odd→x-Even nzero          _ = even-0
Sx-Odd→x-Even (nsucc {n} Nn) h = trans (sym (odd-S (succ₁ n))) h

mutual
  ∸-Even : ∀ {m n} → N m → N n → Even m → Even n → Even (m ∸ n)
  ∸-Even {m} Nm nzero                      h₁ _  = subst Even (sym (∸-x0 m)) h₁
  ∸-Even     nzero          (nsucc {n} Nn) h₁ _  = subst Even (sym (0∸x (nsucc Nn))) h₁
  ∸-Even     (nsucc {m} Nm) (nsucc {n} Nn) h₁ h₂ = prf
    where postulate prf : Even (succ₁ m ∸ succ₁ n)
          {-# ATP prove prf ∸-Odd Sx-Even→x-Odd S∸S #-}

  ∸-Odd : ∀ {m n} → N m → N n → Odd m → Odd n → Even (m ∸ n)
  ∸-Odd nzero          Nn             h₁ _  = ⊥-elim (true≢false (trans (sym h₁) odd-0))
  ∸-Odd (nsucc Nm)     nzero          _  h₂ = ⊥-elim (true≢false (trans (sym h₂) odd-0))
  ∸-Odd (nsucc {m} Nm) (nsucc {n} Nn) h₁ h₂ = prf
    where postulate prf : Even (succ₁ m ∸ succ₁ n)
          {-# ATP prove prf ∸-Even Sx-Odd→x-Even S∸S #-}

x-Even→SSx-Even : ∀ {n} → N n → Even n → Even (succ₁ (succ₁ n))
x-Even→SSx-Even nzero h = prf
  where postulate prf : Even (succ₁ (succ₁ zero))
        {-# ATP prove prf #-}

x-Even→SSx-Even (nsucc {n} Nn) h = prf
  where postulate prf : Even (succ₁ (succ₁ (succ₁ n)))
        {-# ATP prove prf #-}

x+x-Even : ∀ {n} → N n → Even (n + n)
x+x-Even nzero          = subst Even (sym (+-rightIdentity nzero)) even-0
x+x-Even (nsucc {n} Nn) = prf (x+x-Even Nn)
  where postulate prf : Even (n + n) → Even (succ₁ n + succ₁ n)
        {-# ATP prove prf x-Even→SSx-Even +-N +-comm #-}

2x-Even : ∀ {n} → N n → Even (two * n)
2x-Even nzero          = subst Even (sym (*-rightZero 2-N)) even-0
2x-Even (nsucc {n} Nn) = prf
  where
  postulate prf : Even (two * succ₁ n)
  {-# ATP prove prf x-Even→SSx-Even x+x-Even +-N +-comm +-rightIdentity #-}
