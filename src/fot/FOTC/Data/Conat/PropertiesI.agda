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
Conat-pre-fixed : (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')) →
                  ∀ {n} → Conat n
Conat-pre-fixed h = Conat-coind (λ m → m ≡ m) h' refl
  where
  h' : ∀ {m} → m ≡ m → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ m' ≡ m')
  h' _ with h
  ... | inj₁ m≡0            = inj₁ m≡0
  ... | inj₂ (m' , prf , _) = inj₂ (m' , prf , refl)

0-Conat : Conat zero
0-Conat = Conat-coind A h refl
  where
  A : D → Set
  A n = n ≡ zero

  h : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  h An = inj₁ An

-- Adapted from (Sander 1992, p. 57).
∞-Conat : Conat ∞
∞-Conat = Conat-coind A h refl
  where
  A : D → Set
  A n = n ≡ ∞

  h : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  h An = inj₂ (∞ , trans An ∞-eq , refl)

N→Conat : ∀ {n} → N n → Conat n
N→Conat Nn = Conat-coind N h Nn
  where
  h : ∀ {m} → N m → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ N m')
  h nzero          = inj₁ refl
  h (nsucc {m} Nm) = inj₂ (m , refl , Nm)

------------------------------------------------------------------------------
-- References
--
-- Sander, Herbert P. (1992). A Logic of Functional Programs with an
-- Application to Concurrency. PhD thesis. Department of Computer
-- Sciences: Chalmers University of Technology and University of
-- Gothenburg.
