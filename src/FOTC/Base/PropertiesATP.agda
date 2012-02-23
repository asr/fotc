------------------------------------------------------------------------------
-- FOCT terms properties
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Base.PropertiesATP where

open import FOTC.Base

------------------------------------------------------------------------------

postulate
  succInjective : ∀ {d e} → succ₁ d ≡ succ₁ e → d ≡ e
{-# ATP prove succInjective #-}

postulate
  ∷-injective : ∀ {x y xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y ∧ xs ≡ ys
{-# ATP prove ∷-injective #-}
