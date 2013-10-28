------------------------------------------------------------------------------
-- The FOTC co-inductive lists type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- N.B. This module is re-exported by FOTC.Data.Colist.

module FOTC.Data.Colist.Type where

open import FOTC.Base
open import FOTC.Base.List

------------------------------------------------------------------------------
-- The FOTC co-lists type (co-inductive predicate for total list).

-- Functional for the Colist predicate.
-- ColistF : (D → Set) → D → Set
-- ColistF A xs = xs ≡ [] ∨ ∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs'

-- Colist is the greatest fixed-point of ColistF (by Colist-unf and
-- Colist-coind).

postulate
  Colist : D → Set

postulate
-- Colist is a post-fixed point of ColistF, i.e.
--
-- Colist ≤ ColistF Colist.
  Colist-unf : ∀ {xs} → Colist xs →
               xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs')
{-# ATP axiom Colist-unf #-}

-- Colist is the greatest post-fixed point of ColistF, i.e
--
-- ∀ A. A ≤ ColistF A ⇒ A ≤ Colist.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  Colist-coind : ∀ (A : D → Set) {xs} →
                 -- A is post-fixed point of ColistF.
                 (A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')) →
                 -- Colist is greater than A.
                 A xs → Colist xs

-- Because a greatest post-fixed point is a fixed-point, then the
-- Colist predicate is also a pre-fixed point of the functional
-- ColistF, i.e.
--
-- ColistF Colist ≤ Colist.
Colist-pre-fixed : ∀ {xs} →
                   (xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ Colist xs')) →
                   Colist xs
Colist-pre-fixed {xs} h = Colist-coind A prf h
  where
  A : D → Set
  A ws = ws ≡ [] ∨ (∃[ w' ] ∃[ ws' ] ws ≡ w' ∷ ws' ∧ Colist ws')

  prf : A xs → xs ≡ [] ∨ (∃[ x' ] ∃[ xs' ] xs ≡ x' ∷ xs' ∧ A xs')
  prf (inj₁ h₁) = inj₁ h₁
  prf (inj₂ (_ , _ , xs≡x'∷xs' , Axs')) =
    inj₂ (_ , _ , xs≡x'∷xs' , Colist-unf Axs')
