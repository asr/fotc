------------------------------------------------------------------------------
-- Arithmetic properties (added for the Collatz function example)
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Program.Collatz.Data.Nat.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Nat
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesATP
  using ( x≤x
        ; 2*SSx≥2
        )
open import FOTC.Data.Nat.PropertiesATP
  using ( *-N
        ; *-rightZero
        ; *-rightIdentity
        ; x∸x≡0
        ; +-rightIdentity
        ; +-comm
        ; +-N
        ; xy≡0→x≡0∨y≡0
        ; Sx≢x
        ; xy≡1→x≡1
        ; 0∸x
        ; S∸S
        )
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------

^-N : ∀ {m n} → N m → N n → N (m ^ n)
^-N {m} Nm nzero = prf
  where postulate prf : N (m ^ zero)
        {-# ATP prove prf #-}
^-N {m} Nm (nsucc {n} Nn) = prf (^-N Nm Nn)
  where postulate prf : N (m ^ n) → N (m ^ succ₁ n)
        {-# ATP prove prf *-N #-}

div-2x-2≡x : ∀ {n} → N n → div (2' * n) 2' ≡ n
div-2x-2≡x nzero = prf
  where postulate prf : div (2' * zero) 2' ≡ zero
        {-# ATP prove prf *-rightZero #-}
div-2x-2≡x (nsucc nzero) = prf
  where postulate prf : div (2' * (succ₁ zero)) 2' ≡ succ₁ zero
        {-# ATP prove prf *-rightIdentity x≤x x∸x≡0 #-}
div-2x-2≡x (nsucc (nsucc {n} Nn)) = prf (div-2x-2≡x (nsucc Nn))
  where postulate prf : div (2' * succ₁ n) 2' ≡ succ₁ n →
                        div (2' * (succ₁ (succ₁ n))) 2' ≡ succ₁ (succ₁ n)
        {-# ATP prove prf 2*SSx≥2 +-rightIdentity +-comm +-N #-}

postulate div-2^[x+1]-2≡2^x : ∀ {n} → N n → div (2' ^ succ₁ n) 2' ≡ 2' ^ n
{-# ATP prove div-2^[x+1]-2≡2^x ^-N div-2x-2≡x #-}

+∸2 : ∀ {n} → N n → n ≢ zero → n ≢ 1' → n ≡ succ₁ (succ₁ (n ∸ 2'))
+∸2 nzero                  n≢0 n≢1 = ⊥-elim (n≢0 refl)
+∸2 (nsucc nzero)          n≢0 n≢1 = ⊥-elim (n≢1 refl)
+∸2 (nsucc (nsucc {n} Nn)) n≢0 n≢1 = prf
  where
  -- TODO (06 December 2012). We do not use the ATPs because we do not
  -- how to erase a term.
  --
  -- See the interactive proof.
  postulate prf : succ₁ (succ₁ n) ≡ succ₁ (succ₁ (succ₁ (succ₁ n) ∸ 2'))
  -- {-# ATP prove prf S∸S #-}

2^x≢0 : ∀ {n} → N n → 2' ^ n ≢ zero
2^x≢0 nzero          h = ⊥-elim (0≢S (trans (sym h) (^-0 2')))
2^x≢0 (nsucc {n} Nn) h = prf (2^x≢0 Nn)
  where postulate prf : 2' ^ n ≢ zero → ⊥
        {-# ATP prove prf xy≡0→x≡0∨y≡0 ^-N #-}

postulate 2^[x+1]≢1 : ∀ {n} → N n → 2' ^ succ₁ n ≢ 1'
{-# ATP prove 2^[x+1]≢1 Sx≢x xy≡1→x≡1 ^-N #-}

Sx-Even→x-Odd : ∀ {n} → N n → Even (succ₁ n) → Odd n
Sx-Even→x-Odd nzero  h = ⊥-elim prf
  where postulate prf : ⊥
        {-# ATP prove prf #-}
Sx-Even→x-Odd (nsucc {n} Nn) h = prf
  where postulate prf : odd (succ₁ n) ≡ true
        {-# ATP prove prf #-}

Sx-Odd→x-Even : ∀ {n} → N n → Odd (succ₁ n) → Even n
Sx-Odd→x-Even nzero          _ = even-0
Sx-Odd→x-Even (nsucc {n} Nn) h = trans (sym (odd-S (succ₁ n))) h

postulate 2-Even : Even 2'
{-# ATP prove 2-Even #-}

∸-Even : ∀ {m n} → N m → N n → Even m → Even n → Even (m ∸ n)
∸-Odd : ∀ {m n} → N m → N n → Odd m → Odd n → Even (m ∸ n)

∸-Even {m} Nm nzero                      h₁ _  = subst Even (sym (∸-x0 m)) h₁
∸-Even     nzero          (nsucc {n} Nn) h₁ _  = subst Even (sym (0∸x (nsucc Nn))) h₁
∸-Even     (nsucc {m} Nm) (nsucc {n} Nn) h₁ h₂ = prf
  where postulate prf : Even (succ₁ m ∸ succ₁ n)
        {-# ATP prove prf ∸-Odd Sx-Even→x-Odd S∸S #-}

∸-Odd nzero          Nn             h₁ _  = ⊥-elim (t≢f (trans (sym h₁) odd-0))
∸-Odd (nsucc Nm)     nzero          _  h₂ = ⊥-elim (t≢f (trans (sym h₂) odd-0))
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
x+x-Even nzero  = prf
  where postulate prf : even (zero + zero) ≡ true
        {-# ATP prove prf #-}
x+x-Even (nsucc {n} Nn) = prf (x+x-Even Nn)
  where postulate prf : Even (n + n) → Even (succ₁ n + succ₁ n)
        {-# ATP prove prf x-Even→SSx-Even +-N +-comm #-}

2x-Even : ∀ {n} → N n → Even (2' * n)
2x-Even nzero = prf
  where postulate prf : Even (2' * zero)
        {-# ATP prove prf #-}
2x-Even (nsucc {n} Nn) = prf
  where
  postulate prf : Even (2' * succ₁ n)
  {-# ATP prove prf x-Even→SSx-Even x+x-Even +-N +-comm +-rightIdentity #-}

postulate 2^[x+1]-Even : ∀ {n} → N n → Even (2' ^ succ₁ n)
{-# ATP prove 2^[x+1]-Even ^-N 2x-Even #-}
