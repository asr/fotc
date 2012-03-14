------------------------------------------------------------------------------
-- Theorems which require a non-empty domain
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Using the ATPs we don't have to use the postulate about a non-empty
-- domain because the ATPs assume it.

module FOL.NonEmptyDomain.TheoremsATP where

open import FOL.Base

-- References:
-- Elliott Mendelson. Introduction to mathematical logic. Chapman &
-- Hall, 4th edition, 1997.

------------------------------------------------------------------------------
-- We postulate some formulae and propositional functions.
postulate
  A  : Set
  A¹ : D → Set

postulate ∀→∃ : (∀ {x} → A¹ x) → ∃ A¹
{-# ATP prove ∀→∃ #-}

-- Let A be a formula. If x is not free in A then ⊢ (∃x)A ↔ A
-- (Mendelson, 1997, proposition 2.18 (b), p. 70).
postulate ∃-erase-add₁ : ∃ (λ _ → A) ↔ A
{-# ATP prove ∃-erase-add₁ #-}

-- Quantification over a variable that does not occur can be erased or
-- added.
-- TODO: 2012-02-03. The ATPs are not proving the theorem.
postulate ∀-erase-add : ((x : D) → A) ↔ A
-- {-# ATP prove ∀-erase-add #-}

postulate ∃-erase-add₂ : (∃[ x ] A ∨ A¹ x) ↔ A ∨ (∃[ x ] A¹ x)
{-# ATP prove ∃-erase-add₂ #-}
