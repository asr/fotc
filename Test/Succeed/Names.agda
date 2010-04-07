------------------------------------------------------------------------------
-- Testing the translation of function, predicates and variables names
------------------------------------------------------------------------------

-- From the technical manual of TPTP
-- http://www.cs.miami.edu/~tptp/TPTP/TR/TPTPTR.shtml

-- variables start with upper case letters, ... predicates and
-- functors either start with lower case and contain alphanumerics and
-- underscore ...

module Test.Succeed.Names where

infix 4 _≡_

postulate
  D   : Set
  _≡_ : D → D → Set

-- A funny function name.
postulate
  FUN! : D → D

postulate
  -- Using a funny function and variable name
  a₁ : (nx∎ : D) → FUN! nx∎ ≡ nx∎
{-# ATP axiom a₁ #-}

postulate
  foo : (n : D) → FUN! n ≡ n
{-# ATP prove foo #-}

-- A funny predicate name
data PRED! : D → Set where

postulate
  a₂ : (n : D) → PRED! n
{-# ATP axiom a₂ #-}

postulate
  bar : (n : D) → PRED! n
{-# ATP prove bar #-}
