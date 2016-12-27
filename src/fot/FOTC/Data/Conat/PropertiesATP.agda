------------------------------------------------------------------------------
-- Conat properties
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOTC.Data.Conat.PropertiesATP where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Nat

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Conat predicate is also a pre-fixed point of the functional NatF,
-- i.e.
--
-- NatF Conat ≤ Conat (see FOTC.Data.Conat.Type).

-- See Issue https://github.com/asr/apia/issues/81 .
Conat-inA : D → Set
Conat-inA n = n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
{-# ATP definition Conat-inA #-}

Conat-in : ∀ {n} →
           n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n') →
           Conat n
Conat-in h = Conat-coind Conat-inA h' h
  where
  postulate h' : ∀ {n} → Conat-inA n →
                 n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat-inA n')
  {-# ATP prove h' #-}

-- See Issue https://github.com/asr/apia/issues/81 .
0-ConatA : D → Set
0-ConatA n = n ≡ zero
{-# ATP definition 0-ConatA #-}

0-Conat : Conat zero
0-Conat = Conat-coind 0-ConatA h refl
  where
  postulate h : ∀ {n} → 0-ConatA n →
                n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ 0-ConatA n')
  {-# ATP prove h #-}

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
