------------------------------------------------------------------------------
-- Conat properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- References:
--
-- • Sander, Herbert P. (1992). A Logic of Functional Programs with an
--   Application to Concurrency. PhD thesis. Department of Computer
--   Sciences: Chalmers University of Technology and University of
--   Gothenburg.

module FOTC.Data.Conat.PropertiesI where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Nat

------------------------------------------------------------------------------

0-Conat : Conat zero
0-Conat = Conat-coind A prf refl
  where
  A : D → Set
  A n = n ≡ zero

  prf : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  prf An = inj₁ An

-- Adapted from (Sander 1992, p. 57).
∞-Conat : Conat ∞
∞-Conat = Conat-coind A prf refl
  where
  A : D → Set
  A n = n ≡ ∞

  prf : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  prf An = inj₂ (∞ , trans An ∞-eq , refl)

N→Conat : ∀ {n} → N n → Conat n
N→Conat Nn = Conat-coind N prf Nn
  where
  prf : ∀ {m} → N m → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ N m')
  prf nzero          = inj₁ refl
  prf (nsucc {m} Nm) = inj₂ (m , refl , Nm)

-- A different proof.
N→Conat₁ : ∀ {n} → N n → Conat n
N→Conat₁ nzero          = Conat-pre-fixed (inj₁ refl)
N→Conat₁ (nsucc {n} Nn) = Conat-pre-fixed (inj₂ (n , refl , (N→Conat₁ Nn)))
