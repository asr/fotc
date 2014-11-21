{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.Common.FOL.Existential.RequiredWitness where

-- We need to use the existential witness in some proofs based on the
-- non-empty domain hypothesis.

------------------------------------------------------------------------------

postulate
  D   : Set
  D≢∅ : D  -- Non-empty domain.

-- The existential quantifier type on D.
data ∃ (P : D → Set) : Set where
  ∃-intro : ∀ {x} → P x → ∃ P

-- Theorem: Let A be a formula. If x is not free in A then ⊢ (∃x)A ↔ A
-- (Mendelson, 1997, proposition 2.18 (b), p. 70).

-- A version of the right-to-left implication.
l→r : {A : Set} → A → ∃ (λ _ → A)
l→r a = ∃-intro {x = D≢∅} a

------------------------------------------------------------------------------
-- References
--
-- Mendelson, Elliott (1997). Introduction to Mathematical Logic. 4th
-- ed. Chapman & Hall.
