------------------------------------------------------------------------------
-- Conat properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Herbert P. Sander. A logic of functional programs with an
--   application to concurrency. PhD thesis, Chalmers University of
--   Technology and University of Gothenburg, Department of Computer
--   Sciences, 1992.

module FOTC.Data.Conat.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Nat

------------------------------------------------------------------------------

0-Conat : Conat zero
0-Conat = Conat-coind P h refl
  where
  P : D → Set
  P n = n ≡ zero

  h : ∀ {n} → P n → n ≡ zero ∨ (∃[ n' ] P n' ∧ n ≡ succ₁ n')
  h Pn = inj₁ Pn

-- Adapted from (Sander 1992, p. 57).
∞-Conat : Conat ∞
∞-Conat = Conat-coind P h refl
  where
  P : D → Set
  P n = n ≡ ∞

  h : ∀ {n} → P n → n ≡ zero ∨ (∃[ n' ] P n' ∧ n ≡ succ₁ n')
  h Pn = inj₂ (∞ , refl , trans Pn ∞-eq)

N→Conat : ∀ {n} → N n → Conat n
N→Conat Nn = Conat-coind N h Nn
  where
  h : ∀ {m} → N m → m ≡ zero ∨ ∃ (λ m' → N m' ∧ m ≡ succ₁ m')
  h nzero          = inj₁ refl
  h (nsucc {m} Nm) = inj₂ (m , Nm , refl)

-- A different proof.
N→Conat₁ : ∀ {n} → N n → Conat n
N→Conat₁ nzero          = Conat-gfp₃ (inj₁ refl)
N→Conat₁ (nsucc {n} Nn) = Conat-gfp₃ (inj₂ (n , (N→Conat Nn , refl)))
