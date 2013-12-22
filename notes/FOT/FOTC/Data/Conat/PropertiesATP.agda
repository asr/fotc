{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.FOTC.Data.Conat.PropertiesATP where

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
  -- TODO (22 December 2013): The translation failed because we do not
  -- know how erase a term.
  postulate h' : ∀ {m} → m ≡ m → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ m' ≡ m')
  -- {-# ATP prove h' #-}
