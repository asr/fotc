------------------------------------------------------------------------------
-- Co-inductive natural numbers
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module GFPs.Conat where

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
  Conat-out : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')

  -- The higher-order version.
  Conat-out-ho : ∀ {n} → Conat n → NatF Conat n

  -- Conat is the greatest post-fixed point of NatF, i.e.
  --
  -- ∀ A. A ≤ NatF A ⇒ A ≤ Conat.
  Conat-coind :
    (A : D → Set) →
    -- A is post-fixed point of ConatF.
    (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
    -- Conat is greater than A.
    ∀ {n} → A n → Conat n

  -- The higher-order version.
  Conat-coind-ho :
    (A : D → Set) → (∀ {n} → A n → NatF A n) → ∀ {n} → A n → Conat n

  -- 22 December 2013. This is a stronger induction principle. If we
  -- use it, we can use the trivial predicate A = λ x → x ≡ x in the
  -- proofs. Unfortunately, we don't have a justification/proof for
  -- this principle.
  Conat-stronger-coind₁ :
    ∀ (A : D → Set) {n} →
    (A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
    A n → Conat n

  -- Other stronger co-induction principle
  --
  -- Adapted from (Paulson, 1997. p. 16).
  Conat-stronger-coind₂ :
    (A : D → Set) →
    (∀ {n} → A n → (n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) ∨ Conat n) →
    ∀ {n} → A n → Conat n

------------------------------------------------------------------------------
-- Conat-out and Conat-out-ho are equivalents

Conat-out-fo : ∀ {n} → Conat n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
Conat-out-fo = Conat-out-ho

Conat-out-ho' : ∀ {n} → Conat n → NatF Conat n
Conat-out-ho' = Conat-out

------------------------------------------------------------------------------
-- Conat-coind and Conat-coind-ho are equivalents

Conat-coind-fo :
  (A : D → Set) →
  (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
  ∀ {n} → A n → Conat n
Conat-coind-fo = Conat-coind-ho

Conat-coind-ho' :
  (A : D → Set) → (∀ {n} → A n → NatF A n) → ∀ {n} → A n → Conat n
Conat-coind-ho' = Conat-coind

------------------------------------------------------------------------------
-- Because a greatest post-fixed point is a fixed-point, then the
-- Conat predicate is also a pre-fixed point of the functional NatF,
-- i.e.
--
-- NatF Conat ≤ Conat.
Conat-in : ∀ {n} →
           n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n') →
           Conat n
Conat-in h = Conat-coind A h' h
  where
  A : D → Set
  A n = n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')

  h' : ∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')
  h' (inj₁ n≡0)              = inj₁ n≡0
  h' (inj₂ (n' , prf , Cn')) = inj₂ (n' , prf , Conat-out Cn')

-- The higher-order version.
Conat-in-ho : ∀ {n} → NatF Conat n → Conat n
Conat-in-ho = Conat-in

-- A different definition.
Conat-in' : (∀ {n} → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')) →
            ∀ {n} → Conat n
Conat-in' h = Conat-coind (λ m → m ≡ m) h' refl
  where
  h' : ∀ {m} → m ≡ m → m ≡ zero ∨ (∃[ m' ] m ≡ succ₁ m' ∧ m' ≡ m')
  h' _ with h
  ... | inj₁ m≡0            = inj₁ m≡0
  ... | inj₂ (m' , prf , _) = inj₂ (m' , prf , refl)

Conat-in-ho' : (∀ {n} → NatF Conat n) → ∀ {n} → Conat n
Conat-in-ho' = Conat-in'

------------------------------------------------------------------------------
-- From Conat-coind/Conat-stronger-coind₁ to Conat-stronger-coind₁/Conat-coind

Conat-coind'' :
  (A : D → Set) →
  (∀ {n} → A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
  ∀ {n} → A n → Conat n
Conat-coind'' A h An = Conat-stronger-coind₁ A h An

-- 22 December 2013: We couln't prove Conat-stronger-coind₁ using
-- Conat-coind.
Conat-stronger-coind₁' :
  ∀ (A : D → Set) {n} →
  (A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
  A n → Conat n
Conat-stronger-coind₁' A {n} h An = Conat-in (case prf₁ prf₂ (h An))
  where
  prf₁ : n ≡ zero → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
  prf₁ n≡0 = inj₁ n≡0

  prf₂ : ∃[ n' ] n ≡ succ₁ n' ∧ A n' →
         n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ Conat n')
  prf₂ (n' , prf , An') = inj₂ (n' , prf , {!!})

------------------------------------------------------------------------------
-- From Conat-stronger-coind₂ to Conat-stronger-coind₁

-- 13 January 2014: We couln't prove Conat-stronger-coind₁ using
-- Conat-stronger-coind₂.
Conat-stronger-coind₁'' :
  ∀ (A : D → Set) {n} →
  (A n → n ≡ zero ∨ (∃[ n' ] n ≡ succ₁ n' ∧ A n')) →
  A n → Conat n
Conat-stronger-coind₁'' A h An = Conat-stronger-coind₂ A {!!} An

------------------------------------------------------------------------------
-- References
--
-- Paulson, L. C. (1997). Mechanizing Coinduction and Corecursion in
-- Higher-order Logic. Journal of Logic and Computation 7.2,
-- pp. 175–204.
