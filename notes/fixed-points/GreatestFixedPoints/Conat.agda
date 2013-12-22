------------------------------------------------------------------------------
-- Co-inductive natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GreatestFixedPoints.Conat where

open import FOTC.Base
open import FOTC.Base.PropertiesI

------------------------------------------------------------------------------
-- Conat is a greatest fixed-point of a functor

-- The functor.
NatF : (D → Set) → D → Set
NatF A n = n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')

-- The co-natural numbers are the greatest fixed-point of NatF.
postulate
  Conat : D → Set

  -- Conat is a post-fixed point of NatF, i.e.
  --
  -- Conat ≤ NatF Conat.
  Conat-unf : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')

  -- The higher-order version.
  Conat-unf-ho : ∀ {n} → Conat n → NatF Conat n

  -- Conat is the greatest post-fixed point of NatF, i.e
  --
  -- ∀ P. P ≤ NatF P ⇒ P ≤ Conat.
  Conat-coind : ∀ (A : D → Set) →
                (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
                ∀ {n} → A n → Conat n

  -- The higher-order version.
  Conat-coind-ho : ∀ (A : D → Set) →
                   (∀ {n} → A n → NatF A n) →
                   ∀ {n} → A n → Conat n

  Conat-coind-wrong : ∀ (A : D → Set) {n} →
                      -- A is post-fixed point of ConatF.
                      (A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
                      -- Conat is greater than A.
                      A n → Conat n

------------------------------------------------------------------------------
-- Conat-unf and Conat-unf-ho are equivalents

Conat-unf' : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
Conat-unf' = Conat-unf-ho

Conat-unf-ho' : ∀ {n} → Conat n → NatF Conat n
Conat-unf-ho' = Conat-unf

------------------------------------------------------------------------------
-- Conat-coind and Conat-coind-ho are equivalents

Conat-coind' : ∀ (A : D → Set) →
               (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
               ∀ {n} → A n → Conat n
Conat-coind' = Conat-coind-ho

Conat-coind-ho' : ∀ (A : D → Set) →
                  (∀ {n} → A n → NatF A n) →
                  ∀ {n} → A n → Conat n
Conat-coind-ho' = Conat-coind
