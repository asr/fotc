-- Tested with the development version of Agda on 29 February 2012.

module Witness where

-- We need to use the existential witness in some proofs based on the
-- non-empty domain hypothesis.

-- References:

-- Elliott Mendelson. Introduction to mathematical logic. Chapman &
-- Hall, 4th edition, 1997.

------------------------------------------------------------------------------

postulate
  D   : Set
  D≠∅ : D  -- Non-empty domain.

-- The existential quantifier type on D.
data ∃ (P : D → Set) : Set where
  ∃-intro : ∀ {x} → P x → ∃ P

-- Theorem: Let A be a formula. If x is not free in A then ⊢ (∃x)A ↔ A
-- (Mendelson, 1997, proposition 2.18 (b), p. 70).

-- A version of the right-to-left implication.
l→r : {A : Set} → A → ∃ (λ _ → A)
l→r a = ∃-intro {x = D≠∅} a
