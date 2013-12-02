------------------------------------------------------------------------------
-- Conat properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Conat.PropertiesI where

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

  h' : A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  h' _ with h
  ... | inj₁ prf              = inj₁ prf
  ... | inj₂ (n' , n≡Sn' , _) = inj₂ (n' , n≡Sn' , refl)

∞-Conat : Conat ∞
∞-Conat = Conat-coind A h refl
  where
  A : D → Set
  A n = n ≡ n

  h : A ∞ → ∞ ≡ zero ∨ (∃[ n' ] ∞ ≡ succ₁ n' ∧ A n')
  h _ = inj₂ (∞ ,  ∞-eq , refl)

N→Conat : ∀ {n} → N n → Conat n
N→Conat Nn = Conat-coind N h Nn
  where
  h : ∀ {m} → N m → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ N m')
  h nzero          = inj₁ refl
  h (nsucc {m} Nm) = inj₂ (m , refl , Nm)

-- A different proof.
N→Conat' : ∀ {n} → N n → Conat n
N→Conat' nzero          = Conat-pre-fixed (inj₁ refl)
N→Conat' (nsucc {n} Nn) = Conat-pre-fixed (inj₂ (n , refl , (N→Conat' Nn)))
