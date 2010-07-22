------------------------------------------------------------------------------
-- Logical constants (independent use LTC)
------------------------------------------------------------------------------

module Examples.Logic.Constants where

infix  4 ¬_
infixr 3 _∧_
infixr 2 _∨_
infixr 1 _↔_

------------------------------------------------------------------------------
-- The logical constants

-- The logical constants are hard-coded in our implementation,
-- i.e. the following symbols must be used.
postulate
  ⊥ ⊤         : Set -- N.B. the name of the tautology symbol is "\top", not T.
  ¬_          : Set → Set -- N.B. the right hole.
  _∧_ _∨_ _↔_ : Set → Set → Set
  -- We define the implication by Agda function space, i.e. '→'.
