{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module CombiningProofs.ConatPropertiesATP where

open import FOTC.Base
open import FOTC.Data.Conat
open import FOTC.Data.Nat

------------------------------------------------------------------------------

∞-Conat : Conat ∞
∞-Conat = Conat-coind (λ n → n ≡ ∞) h refl
  where
  postulate h : ∀ {n} → n ≡ ∞ → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ n' ≡ ∞)
  {-# ATP prove h #-}
