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

0-Conat : Conat zero
0-Conat = Conat-coind A h refl
  where
  A : D → Set
  A n = n ≡ zero
  {-# ATP definition A #-}

  postulate h : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
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
