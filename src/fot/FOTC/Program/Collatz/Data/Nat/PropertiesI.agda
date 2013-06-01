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
-- Congruence properties

divLeftCong : ∀ {m n o} → m ≡ n → div m o ≡ div n o
divLeftCong refl = refl

divRightCong : ∀ {m n o} → n ≡ o → div m n ≡ div m o
divRightCong refl = refl

------------------------------------------------------------------------------

^-N : ∀ {m n} → N m → N n → N (m ^ n)
^-N {m} Nm nzero          = subst N (sym (^-0 m)) (nsucc nzero)
^-N {m} Nm (nsucc {n} Nn) = subst N (sym (^-S m n)) (*-N Nm (^-N Nm Nn))

div-0-x≡0 : ∀ {n} → N n → n ≢ [0] → div [0] n ≡ [0]
div-0-x≡0 nzero          h = ⊥-elim (h refl)
div-0-x≡0 (nsucc {n} Nn) h = div-x<y h (lt-0S n)

div-x-x≡1 : ∀ {n} → N n → n ≢ [0] → div n n ≡ [1]
div-x-x≡1 {n} Nn h =
  div n n               ≡⟨ div-x≥y h (x≤x Nn) ⟩
  succ₁ (div (n ∸ n) n) ≡⟨ succCong (divLeftCong (x∸x≡0 Nn)) ⟩
  succ₁ (div [0] n)     ≡⟨ succCong (div-0-x≡0 Nn h) ⟩
  [1]                   ∎

div-2x-2≡x : ∀ {n} → N n → div ([2] * n) [2] ≡ n
div-2x-2≡x nzero = prf
  where
  -- See the combined proof.
  postulate prf : div ([2] * zero) [2] ≡ zero

div-2x-2≡x (nsucc nzero) =
  div ([2] * [1]) [2]
    ≡⟨ divLeftCong (*-rightIdentity 2-N) ⟩
  div [2] [2]
    ≡⟨ div-x≥y S≢0 (x≤x 2-N) ⟩
  succ₁ (div ([2] ∸ [2]) [2])
    ≡⟨ succCong (divLeftCong (x∸x≡0 2-N)) ⟩
  succ₁ (div zero [2])
    ≡⟨ succCong (div-x<y S≢0 (lt-0S [1])) ⟩
  [1] ∎

div-2x-2≡x (nsucc (nsucc {n} Nn)) = prf
  where
  -- See the combined proof.
  postulate prf : div ([2] * (succ₁ (succ₁ n))) [2] ≡ succ₁ (succ₁ n)

div-2^[x+1]-2≡2^x : ∀ {n} → N n → div ([2] ^ succ₁ n) [2] ≡ [2] ^ n
div-2^[x+1]-2≡2^x {n} Nn =
  div ([2] ^ succ₁ n) [2]
    ≡⟨ divLeftCong (^-S [2] n) ⟩
  div ([2] * [2] ^ n) [2]
    ≡⟨ div-2x-2≡x (^-N 2-N Nn) ⟩
  [2] ^ n ∎

+∸2 : ∀ {n} → N n → n ≢ zero → n ≢ [1] → n ≡ succ₁ (succ₁ (n ∸ [2]))
+∸2 nzero                  n≢0 _   = ⊥-elim (n≢0 refl)
+∸2 (nsucc nzero)          _   n≢1 = ⊥-elim (n≢1 refl)
+∸2 (nsucc (nsucc {n} Nn)) _   _   = sym prf
  where
  prf : succ₁ (succ₁ (succ₁ (succ₁ n) ∸ [2])) ≡ succ₁ (succ₁ n)
  prf = succ₁ (succ₁ (succ₁ (succ₁ n) ∸ [2]))
          ≡⟨ succCong (succCong (S∸S (nsucc Nn) (nsucc nzero))) ⟩
        succ₁ (succ₁ ((succ₁ n) ∸ [1]))
          ≡⟨ succCong (succCong (S∸S Nn nzero)) ⟩
        succ₁ (succ₁ (n ∸ zero))
          ≡⟨ succCong (succCong (∸-x0 n)) ⟩
        succ₁ (succ₁ n) ∎

x^1≡x : ∀ {n} → N n → n ^ [1] ≡ n
x^1≡x {n} Nn =
  n ^ [1]     ≡⟨ ^-S n [0] ⟩
  n * n ^ [0] ≡⟨ *-rightCong (^-0 n) ⟩
  n * [1]     ≡⟨ *-rightIdentity Nn ⟩
  n           ∎

2^x≢0 : ∀ {n} → N n → [2] ^ n ≢ zero
2^x≢0 nzero          h = ⊥-elim (0≢S (trans (sym h) (^-0 [2])))
2^x≢0 (nsucc {n} Nn) h =
  case (λ 2≡0 → ⊥-elim (0≢S (sym 2≡0)))
       (λ 2^n≡0 → ⊥-elim (2^x≢0 Nn 2^n≡0))
       (xy≡0→x≡0∨y≡0 2-N (^-N 2-N Nn) (trans (sym (^-S [2] n)) h))

2^[x+1]≢1 : ∀ {n} → N n → [2] ^ succ₁ n ≢ [1]
2^[x+1]≢1 {n} Nn h =
  Sx≢x 1-N (xy≡1→x≡1 2-N (^-N 2-N Nn) (trans (sym (^-S [2] n)) h))

Sx-Even→x-Odd : ∀ {n} → N n → Even (succ₁ n) → Odd n
Sx-Even→x-Odd nzero h = ⊥-elim (t≢f (trans₂ (sym h) (even-S zero) odd-0))
Sx-Even→x-Odd (nsucc {n} Nn) h = trans (sym (even-S (succ₁ n))) h

Sx-Odd→x-Even : ∀ {n} → N n → Odd (succ₁ n) → Even n
Sx-Odd→x-Even nzero          _ = even-0
Sx-Odd→x-Even (nsucc {n} Nn) h = trans (sym (odd-S (succ₁ n))) h

∸-Even : ∀ {m n} → N m → N n → Even m → Even n → Even (m ∸ n)
∸-Odd : ∀ {m n} → N m → N n → Odd m → Odd n → Even (m ∸ n)

∸-Even {m} Nm nzero                      h₁ _ = subst Even (sym (∸-x0 m)) h₁
∸-Even     nzero          (nsucc {n} Nn) h₁ _ = subst Even (sym (0∸x (nsucc Nn))) h₁
∸-Even     (nsucc {m} Nm) (nsucc {n} Nn) h₁ h₂ =
  subst Even (sym (S∸S Nm Nn))
        (∸-Odd Nm Nn (Sx-Even→x-Odd Nm h₁) (Sx-Even→x-Odd Nn h₂))

∸-Odd nzero          Nn             h₁ _  = ⊥-elim (t≢f (trans (sym h₁) odd-0))
∸-Odd (nsucc Nm)     nzero          _  h₂ = ⊥-elim (t≢f (trans (sym h₂) odd-0))
∸-Odd (nsucc {m} Nm) (nsucc {n} Nn) h₁ h₂ =
  subst Even (sym (S∸S Nm Nn))
        (∸-Even Nm Nn (Sx-Odd→x-Even Nm h₁) (Sx-Odd→x-Even Nn h₂))

x-Even→SSx-Even : ∀ {n} → N n → Even n → Even (succ₁ (succ₁ n))
x-Even→SSx-Even nzero h =
  even [2]  ≡⟨ even-S [1] ⟩
  odd [1]   ≡⟨ odd-S zero ⟩
  even zero ≡⟨ even-0 ⟩
  true      ∎

x-Even→SSx-Even (nsucc {n} Nn) h =
  even (succ₁ (succ₁ (succ₁ n)))
    ≡⟨ even-S (succ₁ (succ₁ n)) ⟩
  odd (succ₁ (succ₁ n))
    ≡⟨ odd-S (succ₁ n) ⟩
  even (succ₁ n)
    ≡⟨ h ⟩
  true ∎

2-Even : Even [2]
2-Even = x-Even→SSx-Even nzero even-0

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

2x-Even : ∀ {n} → N n → Even ([2] * n)
2x-Even nzero          = subst Even (sym (*-rightZero 2-N)) even-0
2x-Even (nsucc {n} Nn) = subst Even (sym prf)
                               (x-Even→SSx-Even (+-N Nn Nn) (x+x-Even Nn))
  where
  prf : [2] * succ₁ n ≡ succ₁ (succ₁ (n + n))
  prf =
    [2] * succ₁ n
      ≡⟨ *-Sx [1] (succ₁ n) ⟩
    succ₁ n + [1] * succ₁ n
      ≡⟨ +-Sx n ([1] * succ₁ n) ⟩
    succ₁ (n + [1] * succ₁ n)
      ≡⟨ succCong (+-rightCong (*-Sx zero (succ₁ n))) ⟩
    succ₁ (n + (succ₁ n + zero * succ₁ n))
      ≡⟨ succCong (+-rightCong (+-rightCong (*-leftZero (succ₁ n)))) ⟩
    succ₁ (n + (succ₁ n + zero))
      ≡⟨ succCong (+-rightCong (+-rightIdentity (nsucc Nn))) ⟩
    succ₁ (n + succ₁ n)
      ≡⟨ succCong (+-comm Nn (nsucc Nn)) ⟩
    succ₁ (succ₁ n + n)
      ≡⟨ succCong (+-Sx n n) ⟩
    succ₁ (succ₁ (n + n)) ∎

2^[x+1]-Even : ∀ {n} → N n → Even ([2] ^ succ₁ n)
2^[x+1]-Even {n} Nn = subst Even (sym (^-S [2] n)) (2x-Even (^-N 2-N Nn))
