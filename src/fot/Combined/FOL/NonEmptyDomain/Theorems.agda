------------------------------------------------------------------------------
-- Theorems which require a non-empty domain
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOL.NonEmptyDomain.Theorems where

open import Combined.FOL.Base

------------------------------------------------------------------------------
-- We postulate some formulae and propositional functions.
postulate
  A  : Set
  A¹ : D → Set

postulate ∀→∃ : (∀ {x} → A¹ x) → ∃ A¹
{-# ATP prove ∀→∃ #-}

-- Let A be a formula. If x is not free in A then ⊢ (∃x)A ↔ A [van
-- Dalen, 2013, Theorem 3.5.2.iv, p 69].
postulate ∃-erase-add₁ : (∃[ _ ] A) ↔ A
{-# ATP prove ∃-erase-add₁ #-}

-- Quantification over a variable that does not occur can be erased or
-- added.
postulate ∀-erase-add : ((x : D) → A) ↔ A
{-# ATP prove ∀-erase-add #-}

postulate ∃-erase-add₂ : (∃[ x ] (A ∨ A¹ x)) ↔ A ∨ (∃[ x ] A¹ x)
{-# ATP prove ∃-erase-add₂ #-}

------------------------------------------------------------------------------
-- References
--
-- van Dalen, Dirk (2013). Logic and Structure. 5th ed. Springer.

