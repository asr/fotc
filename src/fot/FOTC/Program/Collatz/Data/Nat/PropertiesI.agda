------------------------------------------------------------------------------
-- Arithmetic properties (added for the Collatz function example)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Program.Collatz.Data.Nat.PropertiesI where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base
open import FOTC.Base.PropertiesI
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.TotalityI
open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------

^-N : ∀ {m n} → N m → N n → N (m ^ n)
^-N {m} Nm nzero          = subst N (sym (^-0 m)) (nsucc nzero)
^-N {m} Nm (nsucc {n} Nn) = subst N (sym (^-S m n)) (*-N Nm (^-N Nm Nn))

2x/2≡x : ∀ {n} → N n → two * n / two ≡ n
2x/2≡x nzero = prf
  where
  -- See the combined proof.
  postulate prf : two * zero / two ≡ zero

2x/2≡x (nsucc nzero) =
  (two * succ₁ zero) / two
    ≡⟨ cong₂ _/_ (*-rightIdentity 2-N) refl ⟩
  two / two
    ≡⟨ /-x≥y (x≥x 2-N) ⟩
  succ₁ ((two ∸ two) / two)
    ≡⟨ succCong (cong₂ _/_ (x∸x≡0 2-N) refl) ⟩
  succ₁ (zero / two)
    ≡⟨ succCong (/-x<y (lt-0S (succ₁ zero))) ⟩
  succ₁ zero ∎

2x/2≡x (nsucc (nsucc {n} Nn)) = prf
  where
  -- See the combined proof.
  postulate prf : two * succ₁ (succ₁ n) / two ≡ succ₁ (succ₁ n)

2^[x+1]/2≡2^x : ∀ {n} → N n → (two ^ (succ₁ n)) / two ≡ two ^ n
2^[x+1]/2≡2^x {n} Nn =
  two ^ (succ₁ n) / two
    ≡⟨ subst (λ t → two ^ (succ₁ n) / two ≡ t / two) (^-S two n) refl ⟩
  (two * two ^ n) / two
    ≡⟨ 2x/2≡x (^-N 2-N Nn) ⟩
  two ^ n ∎

Sx≡2^0→x≡0 : ∀ {n} → N n → succ₁ n ≡ two ^ zero → n ≡ zero
Sx≡2^0→x≡0 nzero         _       = refl
Sx≡2^0→x≡0(nsucc {n} Nn) SSn≡2^0 =
  ⊥-elim (0≢S (sym (succInjective (trans SSn≡2^0 (^-0 two)))))

+∸2 : ∀ {n} → N n → n ≢ zero → n ≢ one → n ≡ succ₁ (succ₁ (n ∸ two))
+∸2 nzero                  n≢0 n≢1 = ⊥-elim (n≢0 refl)
+∸2 (nsucc nzero)          n≢0 n≢1 = ⊥-elim (n≢1 refl)
+∸2 (nsucc (nsucc {n} Nn)) n≢0 n≢1 = sym prf
  where
  prf : succ₁ (succ₁ (succ₁ (succ₁ n) ∸ two)) ≡ succ₁ (succ₁ n)
  prf = succ₁ (succ₁ (succ₁ (succ₁ n) ∸ two))
          ≡⟨ succCong (succCong (S∸S (nsucc Nn) (nsucc nzero))) ⟩
        succ₁ (succ₁ ((succ₁ n ) ∸ (succ₁ zero)))
          ≡⟨ succCong (succCong (S∸S Nn nzero)) ⟩
        succ₁ (succ₁ (n ∸ zero))
          ≡⟨ succCong (succCong (∸-x0 n)) ⟩
        succ₁ (succ₁ n) ∎

2^x≢0 : ∀ {n} → N n → two ^ n ≢ zero
2^x≢0 nzero          h = ⊥-elim (0≢S (trans (sym h) (^-0 two)))
2^x≢0 (nsucc {n} Nn) h =
  case (λ 2≡0 → ⊥-elim (0≢S (sym 2≡0)))
       (λ 2^n≡0 → ⊥-elim (2^x≢0 Nn 2^n≡0))
       (xy≡0→x≡0∨y≡0 2-N (^-N 2-N Nn) (trans (sym (^-S two n)) h))

2^[x+1]≢1 : ∀ {n} → N n → two ^ (succ₁ n) ≢ one
2^[x+1]≢1 {n} Nn h =
  Sx≢x (nsucc nzero) (xy≡1→x≡1 2-N (^-N 2-N Nn) (trans (sym (^-S two n)) h))

Sx-Even→x-Odd : ∀ {n} → N n → Even (succ₁ n) → Odd n
Sx-Even→x-Odd nzero          h = ⊥-elim (true≢false
                                       (trans₂ (sym h) (even-S zero) odd-0))
Sx-Even→x-Odd (nsucc {n} Nn) h = trans (sym (even-S (succ₁ n))) h

Sx-Odd→x-Even : ∀ {n} → N n → Odd (succ₁ n) → Even n
Sx-Odd→x-Even nzero          _ = even-0
Sx-Odd→x-Even (nsucc {n} Nn) h = trans (sym (odd-S (succ₁ n))) h

mutual
  ∸-Even : ∀ {m n} → N m → N n → Even m → Even n → Even (m ∸ n)
  ∸-Even {m} Nm nzero                      h₁ _ = subst Even (sym (∸-x0 m)) h₁
  ∸-Even     nzero          (nsucc {n} Nn) h₁ _ = subst Even (sym (0∸x (nsucc Nn))) h₁
  ∸-Even     (nsucc {m} Nm) (nsucc {n} Nn) h₁ h₂ =
    subst Even (sym (S∸S Nm Nn))
          (∸-Odd Nm Nn (Sx-Even→x-Odd Nm h₁) (Sx-Even→x-Odd Nn h₂))

  ∸-Odd : ∀ {m n} → N m → N n → Odd m → Odd n → Even (m ∸ n)
  ∸-Odd nzero          Nn             h₁ _  = ⊥-elim (true≢false (trans (sym h₁) odd-0))
  ∸-Odd (nsucc Nm)     nzero          _  h₂ = ⊥-elim (true≢false (trans (sym h₂) odd-0))
  ∸-Odd (nsucc {m} Nm) (nsucc {n} Nn) h₁ h₂ =
    subst Even (sym (S∸S Nm Nn))
          (∸-Even Nm Nn (Sx-Odd→x-Even Nm h₁) (Sx-Odd→x-Even Nn h₂))

x-Even→SSx-Even : ∀ {n} → N n → Even n → Even (succ₁ (succ₁ n))
x-Even→SSx-Even nzero h =
  even (succ₁ (succ₁ zero))
    ≡⟨ even-S (succ₁ zero) ⟩
  odd (succ₁ zero)
    ≡⟨ odd-S zero ⟩
  even zero
    ≡⟨ even-0 ⟩
  true ∎

x-Even→SSx-Even (nsucc {n} Nn) h =
  even (succ₁ (succ₁ (succ₁ n)))
    ≡⟨ even-S (succ₁ (succ₁ n)) ⟩
  odd (succ₁ (succ₁ n))
    ≡⟨ odd-S (succ₁ n) ⟩
  even (succ₁ n)
    ≡⟨ h ⟩
  true ∎

x+x-Even : ∀ {n} → N n → Even (n + n)
x+x-Even nzero          = subst Even (sym (+-rightIdentity nzero)) even-0
x+x-Even (nsucc {n} Nn) = subst Even (sym prf)
                             (x-Even→SSx-Even (+-N Nn Nn) (x+x-Even Nn))
  where
  prf : succ₁ n + succ₁ n ≡ succ₁ (succ₁ (n + n))
  prf = succ₁ n + succ₁ n
          ≡⟨ +-Sx n (succ₁ n) ⟩
        succ₁ (n + succ₁ n)
          ≡⟨ succCong (+-comm Nn (nsucc Nn)) ⟩
        succ₁ (succ₁ n + n)
          ≡⟨ succCong (+-Sx n n) ⟩
        succ₁ (succ₁ (n + n)) ∎

2x-Even : ∀ {n} → N n → Even (two * n)
2x-Even nzero          = subst Even (sym (*-rightZero 2-N)) even-0
2x-Even (nsucc {n} Nn) = subst Even (sym prf)
                            (x-Even→SSx-Even (+-N Nn Nn) (x+x-Even Nn))
  where
  prf : succ₁ (succ₁ zero) * succ₁ n ≡ succ₁ (succ₁ (n + n))
  prf =
    succ₁ (succ₁ zero) * succ₁ n
      ≡⟨ *-Sx (succ₁ zero) (succ₁ n) ⟩
    succ₁ n + succ₁ zero * succ₁ n
      ≡⟨ +-Sx n (succ₁ zero * succ₁ n) ⟩
    succ₁ (n + succ₁ zero * succ₁ n)
      ≡⟨ succCong (cong (_+_ n) (*-Sx zero (succ₁ n))) ⟩
    succ₁ (n + (succ₁ n + zero * succ₁ n))
      ≡⟨ succCong (cong (_+_ n) (cong (_+_ (succ₁ n)) (*-leftZero (succ₁ n)))) ⟩
    succ₁ (n + (succ₁ n + zero))
      ≡⟨ succCong (cong (_+_ n) (+-rightIdentity (nsucc Nn))) ⟩
    succ₁ (n + succ₁ n)
      ≡⟨ succCong (+-comm Nn (nsucc Nn)) ⟩
    succ₁ (succ₁ n + n)
      ≡⟨ succCong (+-Sx n n) ⟩
    succ₁ (succ₁ (n + n)) ∎

2^[x+1]-Even : ∀ {n} → N n → Even (two ^ (succ₁ n))
2^[x+1]-Even {n} Nn = subst Even (sym (^-S two n)) (2x-Even (^-N 2-N Nn))
