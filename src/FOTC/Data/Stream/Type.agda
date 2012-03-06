------------------------------------------------------------------------------
-- The FOTC stream type
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOTC.Data.Stream.Type where

open import FOTC.Base

------------------------------------------------------------------------------
-- Functional for the FOTC Stream type.
-- StreamF : (D → Set) → D → Set
-- StreamF P xs = ∃[ x' ] ∃[ xs' ] P xs' ∧ xs ≡ x' ∷ xs'

-- Stream is the greatest fixed-point of StreamF (by Stream-gfp₁ and
-- Stream-gfp₂).

postulate
  Stream : D → Set

postulate
-- Stream is a post-fixed point of StreamF, i.e.
--
-- Stream ≤ StreamF Stream.
  Stream-gfp₁ : ∀ {xs} → Stream xs →
                ∃[ x' ] ∃[ xs' ] Stream xs' ∧ xs ≡ x' ∷ xs'
{-# ATP axiom Stream-gfp₁ #-}

-- Stream is the greatest post-fixed point of StreamF, i.e
--
-- ∀ P. P ≤ StreamF P ⇒ P ≤ Stream.
--
-- N.B. This is an axiom schema. Because in the automatic proofs we
-- *must* use an instance, we do not add this postulate as an ATP
-- axiom.
postulate
  Stream-gfp₂ : (P : D → Set) →
                -- P is post-fixed point of StreamF.
                (∀ {xs} → P xs → ∃[ x' ] ∃[ xs' ] P xs' ∧ xs ≡ x' ∷ xs') →
                -- Stream is greater than P.
                ∀ {xs} → P xs → Stream xs

-- Because a greatest post-fixed point is a fixed-point, then the
-- Stream predicate is also a pre-fixed point of the functor StreamF, i.e.
--
-- StreamF Stream ≤ Stream.
Stream-gfp₃ : ∀ {xs} →
              (∃[ x' ] ∃[ xs' ] Stream xs' ∧ xs ≡ x' ∷ xs') →
              Stream xs
Stream-gfp₃ h = Stream-gfp₂ P helper h
  where
  P : D → Set
  P ws = ∃[ w' ] ∃[ ws' ] Stream ws' ∧ ws ≡ w' ∷ ws'

  helper : ∀ {xs} → P xs → ∃[ x' ] ∃[ xs' ] P xs' ∧ xs ≡ x' ∷ xs'
  helper (_ , _ , Sxs' , xs≡x'∷xs') = _ , _ , Stream-gfp₁ Sxs' , xs≡x'∷xs'
