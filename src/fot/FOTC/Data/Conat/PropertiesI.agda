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
0-Conat = Conat-gfp₂ P helper refl
  where
  P : D → Set
  P n = n ≡ zero

  helper : ∀ {n} → P n → n ≡ zero ∨ (∃[ n' ] P n' ∧ n ≡ succ₁ n')
  helper Pn = inj₁ Pn

-- Adapted from (Sander 1992, p. 57).
ω-Conat : Conat ω
ω-Conat = Conat-gfp₂ P helper refl
  where
  P : D → Set
  P n = n ≡ ω

  helper : ∀ {n} → P n → n ≡ zero ∨ (∃[ n' ] P n' ∧ n ≡ succ₁ n')
  helper Pn = inj₂ (ω , refl , trans Pn ω-eq)

N→Conat : ∀ {n} → N n → Conat n
N→Conat Nn = Conat-gfp₂ N helper Nn
  where
  helper : ∀ {m} → N m → m ≡ zero ∨ ∃ (λ m' → N m' ∧ m ≡ succ₁ m')
  helper nzero          = inj₁ refl
  helper (nsucc {m} Nm) = inj₂ (m , Nm , refl)

-- A different proof.
N→Conat₁ : ∀ {n} → N n → Conat n
N→Conat₁ nzero          = Conat-gfp₃ (inj₁ refl)
N→Conat₁ (nsucc {n} Nn) = Conat-gfp₃ (inj₂ (n , (N→Conat Nn , refl)))
