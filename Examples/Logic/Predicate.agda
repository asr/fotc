------------------------------------------------------------------------------
-- Predicate logic examples
------------------------------------------------------------------------------

-- This module contains some examples showing the use of the ATPs to
-- prove theorems from predicate logic.

module Examples.Logic.Predicate where

------------------------------------------------------------------------------

postulate
  D  : Set
  P  : D → Set
  ∃D : (P : D → Set) → Set

-- This theorem cannot prove in Coq because in Coq we can have empty
-- domains. We do not have this problem because the ATPs assume a
-- non-empty domain.
postulate
  thm₁ : (d : D) → P d → ∃D (λ e → P e)
{-# ATP prove thm₁ #-}
