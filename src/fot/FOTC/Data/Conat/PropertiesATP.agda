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
-- Because a greatest post-fixed point is a fixed-point, then the
-- Conat predicate is also a pre-fixed point of the functional NatF,
-- i.e,
--
-- NatF Conat ≤ Conat (see FOTC.Data.Conat.Type).
Conat-pre-fixed : ∀ {n} →
                  (n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')) →
                  Conat n
Conat-pre-fixed {n} h = Conat-coind A h' refl
  where
  A : D → Set
  A m = m ≡ m
  {-# ATP definition A #-}

  postulate h' : A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  {-# ATP prove h' #-}

0-Conat : Conat zero
0-Conat = Conat-coind A h refl
  where
  A : D → Set
  A n = n ≡ zero
  {-# ATP definition A #-}

  postulate h : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  {-# ATP prove h #-}

-- Adapted from (Sander 1992, p. 57).
∞-Conat : Conat ∞
∞-Conat = Conat-coind A h refl
  where
  A : D → Set
  A n = n ≡ ∞
  {-# ATP definition A #-}

  postulate h : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  {-# ATP prove h #-}

N→Conat : ∀ {n} → N n → Conat n
N→Conat Nn = Conat-coind N h Nn
  where
  h : ∀ {m} → N m → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ N m')
  h nzero = prf
    where postulate prf : zero ≡ zero ∨ (∃[ m' ] zero ≡ succ₁ m' ∧ N m')
          {-# ATP prove prf #-}
  h (nsucc {m} Nm) = prf
    where postulate prf : succ₁ m ≡ zero ∨ (∃[ m' ] succ₁ m ≡ succ₁ m' ∧ N m')
          {-# ATP prove prf #-}
