------------------------------------------------------------------------------
-- Logical constants
------------------------------------------------------------------------------

module Examples.Logic.Constants where

infix  5 ¬_
infixr 4 _∧_
infixr 3 _∨_
infixr 2 _⇒_
infixr 1 _↔_

------------------------------------------------------------------------------
-- The logical connectives

-- The logical connectives are hard-coded in our implementation,
-- i.e. the following symbols must be used.
postulate
  ⊥ ⊤     : Set  -- N.B. the name of the tautology symbol is "\top", not T.
  ¬_      : Set → Set  -- N.B. the right hole.
  _∧_ _∨_ : Set → Set → Set
  _⇒_ _↔_ : Set → Set → Set

-- The quantifiers

postulate
  D : Set  -- The universe of discourse.

-- The quantifiers are hard-coded in our implementation, i.e. the
-- following symbols must be used.
postulate
  ∃D : (P : D → Set) → Set
  ∀D : (P : D → Set) → Set
