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

module FOTC.Data.Conat.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Nat

------------------------------------------------------------------------------

0-Conat : Conat zero
0-Conat = Conat-coind P helper refl
  where
  P : D → Set
  P n = n ≡ zero
  {-# ATP definition P #-}

  postulate helper : ∀ {n} → P n → n ≡ zero ∨ (∃[ n' ] P n' ∧ n ≡ succ₁ n')
  {-# ATP prove helper #-}

-- Adapted from (Sander 1992, p. 57).
ω-Conat : Conat ω
ω-Conat = Conat-coind P helper refl
  where
  P : D → Set
  P n = n ≡ ω
  {-# ATP definition P #-}

  postulate helper : ∀ {n} → P n → n ≡ zero ∨ (∃[ n' ] P n' ∧ n ≡ succ₁ n')
  {-# ATP prove helper #-}

N→Conat : ∀ {n} → N n → Conat n
N→Conat Nn = Conat-coind N helper Nn
  where
  helper : ∀ {m} → N m → m ≡ zero ∨ ∃ (λ m' → N m' ∧ m ≡ succ₁ m')
  helper nzero          = inj₁ refl
  helper (nsucc {m} Nm) = inj₂ (m , Nm , refl)
