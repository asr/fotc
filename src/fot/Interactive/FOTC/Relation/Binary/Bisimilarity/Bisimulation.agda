------------------------------------------------------------------------------
-- Bisimulation on unbounded lists
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- In FOTC, we won't use the bisimulation functional on unbounded
-- lists. This module is only for illustrative purposes.

module Interactive.FOTC.Relation.Binary.Bisimilarity.Bisimulation where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Relation.Binary.Bisimilarity.Type
open import Interactive.FOTC.Relation.Binary.Bisimilarity.Properties

----------------------------------------------------------------------------
-- The bisimilarity relation _≈_ on unbounded lists is the greatest
-- post-fixed point of Bisimulation (by post-fp and gpfp).

-- The bisimulation functional on unbounded lists (adapted from Dybjer
-- and Sander 1989, p. 310 and Jacobs and Rutten 1997, p. 30).
BisimulationF : (D → D → Set) → D → D → Set
BisimulationF B xs ys =
  ∃[ x' ] ∃[ xs' ] ∃[ ys' ] xs ≡ x' ∷ xs' ∧ ys ≡ x' ∷ ys' ∧ B xs' ys'

-- The bisimilarity relation _≈_ on unbounded lists is a post-fixed
-- point of Bisimulation, i.e.
--
-- _≈_ ≤ Bisimulation _≈_.
post-fp : ∀ {xs ys} → xs ≈ ys → BisimulationF _≈_ xs ys
post-fp = ≈-out

-- The bisimilarity relation _≈_ on unbounded lists is the greatest
-- post-fixed point of Bisimulation, i.e.
 --
-- ∀ B. B ≤ Bisimulation B ⇒ B ≤ _≈_.
greatest-post-fp :
  (B : D → D → Set) →
  -- B is a post-fixed point of Bisimulation.
  (∀ {xs} {ys} → B xs ys → BisimulationF B xs ys) →
  -- _≈_ is greater than B.
  ∀ {xs} {ys} → B xs ys → xs ≈ ys
greatest-post-fp = ≈-coind

-- Because a greatest post-fixed point is a fixed-point, the
-- bisimilarity relation _≈_ on unbounded lists is also a pre-fixed
-- point of Bisimulation, i.e.
--
-- Bisimulation _≈_ ≤ _≈_.
pre-fp : ∀ {xs} {ys} → BisimulationF _≈_ xs ys → xs ≈ ys
pre-fp = ≈-in

----------------------------------------------------------------------------
-- References
--
-- Dybjer, Peter and Sander, Herbert P. (1989). A Functional
-- Programming Approach to the Specification and Verification of
-- Concurrent Systems. Formal Aspects of Computing 1, pp. 303–319.
--
-- Jacobs, Bart and Rutten, Jan (1997). A Tutorial on (Co)Algebras and
-- (Co)Induction. EATCS Bulletin 62, pp. 222–259.
