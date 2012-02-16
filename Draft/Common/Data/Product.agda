-----------------------------------------------------------------------------
-- Classical existential elimination
-----------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Draft.Common.Data.Product where

-- We add 3 to the fixities of the standard library.
infixr 7 _,_

-----------------------------------------------------------------------------
-- Existential elimination
--     ∃x.P(x)   P(x) → Q
--  ------------------------
--             Q

postulate
  D : Set

-- The existential quantifier type on D.
data ∃ (P : D → Set) : Set where
  _,_ : (x : D) → P x → ∃ P

-- The existential elimination.

-- NB. We do not use the usual type theory elimination with two
-- projections because we are working in first-order logic where we
-- cannot extract a term from an existence proof.
∃-elim : {P : D → Set}{Q : Set} → ∃ P → ((x : D) → P x → Q) → Q
∃-elim (x , p) h = h x p
