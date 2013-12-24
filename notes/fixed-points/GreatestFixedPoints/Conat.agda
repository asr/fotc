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
  Conat-coind :
    ∀ (A : D → Set) →
    -- A is post-fixed point of ConatF.
    (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
    -- Conat is greater than A.
    ∀ {n} → A n → Conat n

  -- The higher-order version.
  Conat-coind-ho :
    ∀ (A : D → Set) → (∀ {n} → A n → NatF A n) → ∀ {n} → A n → Conat n

  -- 22 December 2013. This is a stronger induction principle. If we
  -- use it, we can use the trivial A = λ x → x ≡ x in the
  -- proofs. Unfortunately, we don't have a justification for this
  -- principle.
  Conat-coind-stronger :
    ∀ (A : D → Set) {n} →
    (A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
    A n → Conat n

------------------------------------------------------------------------------
-- Conat-unf and Conat-unf-ho are equivalents

Conat-unf' : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
Conat-unf' = Conat-unf-ho

Conat-unf-ho' : ∀ {n} → Conat n → NatF Conat n
Conat-unf-ho' = Conat-unf

------------------------------------------------------------------------------
-- Conat-coind and Conat-coind-ho are equivalents

Conat-coind' :
  ∀ (A : D → Set) →
  (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
  ∀ {n} → A n → Conat n
Conat-coind' = Conat-coind-ho

Conat-coind-ho' :
  ∀ (A : D → Set) → (∀ {n} → A n → NatF A n) → ∀ {n} → A n → Conat n
Conat-coind-ho' = Conat-coind

------------------------------------------------------------------------------
-- From Conat-coind/Conat-coind-stronger to Conat-coind-stronger/Conat-coind

Conat-coind'' :
  ∀ (A : D → Set) →
  (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
  ∀ {n} → A n → Conat n
Conat-coind'' A h An = Conat-coind-stronger A h An

-- 22 December 2013: We cannot prove Conat-coind-stronger using
-- Conat-coind.
Conat-coind-stronger'' :
  ∀ (A : D → Set) {n} →
  (A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
  A n → Conat n
Conat-coind-stronger'' A h An = Conat-coind A {!!} An

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Conat predicate is also a pre-fixed point of the functional NatF,
-- i.e,
--
-- NatF Conat ≤ Conat.
Conat-pre-fixed : ∀ {n} →
                  n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n') →
                  Conat n
Conat-pre-fixed h = Conat-coind A h' h
  where
  A : D → Set
  A n = n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')

  h' : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  h' (inj₁ n≡0)              = inj₁ n≡0
  h' (inj₂ (n' , prf , Cn')) = inj₂ (n' , prf , Conat-unf Cn')

Conat-pre-fixed-ho : ∀ {n} → NatF Conat n → Conat n
Conat-pre-fixed-ho = Conat-pre-fixed

-- A different definition.
Conat-pre-fixed' : (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')) →
                   ∀ {n} → Conat n
Conat-pre-fixed' h = Conat-coind (λ m → m ≡ m) h' refl
  where
  h' : ∀ {m} → m ≡ m → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ m' ≡ m')
  h' _ with h
  ... | inj₁ m≡0            = inj₁ m≡0
  ... | inj₂ (m' , prf , _) = inj₂ (m' , prf , refl)

Conat-pre-fixed-ho' : (∀ {n} → NatF Conat n) → ∀ {n} → Conat n
Conat-pre-fixed-ho' = Conat-pre-fixed'
