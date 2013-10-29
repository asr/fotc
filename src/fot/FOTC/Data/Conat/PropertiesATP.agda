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

module FOTC.Data.Conat.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Nat

------------------------------------------------------------------------------

0-Conat : Conat zero
0-Conat = Conat-coind A prf refl
  where
  A : D → Set
  A n = n ≡ zero
  {-# ATP definition A #-}

  postulate prf : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  {-# ATP prove prf #-}

-- Adapted from (Sander 1992, p. 57).
∞-Conat : Conat ∞
∞-Conat = Conat-coind A prf refl
  where
  A : D → Set
  A n = n ≡ ∞
  {-# ATP definition A #-}

  postulate prf : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  {-# ATP prove prf #-}

N→Conat : ∀ {n} → N n → Conat n
N→Conat Nn = Conat-coind N prf Nn
  where
  prf : ∀ {m} → N m → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ N m')
  prf nzero = prf₁
    where postulate prf₁ : zero ≡ zero ∨ (∃[ m' ] zero ≡ succ₁ m' ∧ N m')
          {-# ATP prove prf₁ #-}
  prf (nsucc {m} Nm) = prf₂
    where postulate prf₂ : succ₁ m ≡ zero ∨ (∃[ m' ] succ₁ m ≡ succ₁ m' ∧ N m')
          {-# ATP prove prf₂ #-}
