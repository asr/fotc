------------------------------------------------------------------------------
-- Co-inductive natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- We want to represent the total natural numbers data type
--
-- data N : D → Set where
--   nzero : N zero
--   nsucc : ∀ {n} → N n → N (succ₁ n)
--
-- using the representation of N as the least fixed-point.

module GreatestFixedPoints.Conat where

open import FOTC.Base
open import FOTC.Base.PropertiesI

------------------------------------------------------------------------------
-- Conat is a greatest fixed-point of a functor

-- The functor.
NatF : (D → Set) → D → Set
NatF P n = n ≡ zero ∨ (∃[ n' ] P n' ∧ n ≡ succ₁ n')

-- The co-natural numbers are the greatest fixed-point of NatF.
postulate
  Conat : D → Set

  -- Conat is a post-fixed point of NatF, i.e.
  --
  -- Conat ≤ NatF Conat.
  Conat-unf : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] Conat n' ∧ n ≡ succ₁ n')

  -- The higher-order version.
  Conat-unf-ho : ∀ {n} → Conat n → NatF Conat n
  -- Conat is the greatest post-fixed point of NatF, i.e
  --
  -- ∀ P. P ≤ NatF P ⇒ P ≤ Conat.

  Conat-coind : ∀ (A : D → Set) {n} →
                -- A is post-fixed point of ConatF.
                (A n → n ≡ zero ∨ (∃[ n' ] A n' ∧ n ≡ succ₁ n')) →
                -- Conat is greater than A.
                A n → Conat n

  -- The higher-order version.
  Conat-coind-ho : ∀ (A : D → Set) {n} →
                   (A n → NatF A n) →
                   A n → Conat n

  -- A different co-induction principle.
  Conat-coind-old : ∀ (A : D → Set) →
                    (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] A n' ∧ n ≡ succ₁ n')) →
                    ∀ {n} → A n → Conat n

------------------------------------------------------------------------------
-- Conat-unf and Conat-unf-ho are equivalents

Conat-unf' : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] Conat n' ∧ n ≡ succ₁ n')
Conat-unf' = Conat-unf-ho

Conat-unf-ho' : ∀ {n} → Conat n → NatF Conat n
Conat-unf-ho' = Conat-unf

------------------------------------------------------------------------------
-- Conat-coind and Conat-coind-ho are equivalents

Conat-coind' : ∀ (A : D → Set) {n} →
               (A n → n ≡ zero ∨ (∃[ n' ] A n' ∧ n ≡ succ₁ n')) →
               A n → Conat n
Conat-coind' = Conat-coind-ho

Conat-coind-ho' : ∀ (A : D → Set) {n} →
                  (A n → NatF A n) →
                  A n → Conat n
Conat-coind-ho' = Conat-coind

------------------------------------------------------------------------------
-- From/to Conat-coind/Conat-coind-old

Conat-coind-old' : ∀ (A : D → Set) →
                   (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] A n' ∧ n ≡ succ₁ n')) →
                   ∀ {n} → A n → Conat n
Conat-coind-old' A h = Conat-coind A h

-- 26 January 2013. We cannot prove Conat-coind using Conat-coind-old.
Conat-coind'' : ∀ (A : D → Set) {n} →
                (A n → n ≡ zero ∨ (∃[ n' ] A n' ∧ n ≡ succ₁ n')) →
                A n → Conat n
Conat-coind'' A h An = Conat-coind-old A {!!} An
