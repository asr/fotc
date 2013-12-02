------------------------------------------------------------------------------
-- Conat properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

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
Conat-pre-fixed {n} h = Conat-coind (λ m → m ≡ m) h' refl
  where
  postulate h' : n ≡ n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ n' ≡ n')
  {-# ATP prove h' #-}

0-Conat : Conat zero
0-Conat = Conat-coind (λ n → n ≡ n) h refl
  where
  postulate h : zero ≡ zero → zero ≡ zero ∨ (∃[ n ] zero ≡ succ₁ n ∧ n ≡ n)
  {-# ATP prove h #-}

∞-Conat : Conat ∞
∞-Conat = Conat-coind (λ n → n ≡ n) h refl
  where
  postulate h : ∞ ≡ ∞ → ∞ ≡ zero ∨ (∃[ n ] ∞ ≡ succ₁ n ∧ n ≡ n)
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
