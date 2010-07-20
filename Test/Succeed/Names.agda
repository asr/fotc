------------------------------------------------------------------------------
-- Testing the translation of function, predicates and variables names
------------------------------------------------------------------------------

-- From the technical manual of TPTP
-- (http://www.cs.miami.edu/~tptp/TPTP/TR/TPTPTR.shtml)

-- ... variables start with upper case letters, ... predicates and
-- functors either start with lower case and contain alphanumerics and
-- underscore ...

module Test.Succeed.Names where

infix 4 _≡_

------------------------------------------------------------------------------
-- Testing funny names

postulate
  D     : Set
  _≡_   : D → D → Set
  FUN!  : D → D   -- A funny function name
  PRED! : D → Set -- A funny predicate name

postulate
  -- Using a funny function and variable name
  funnyFV  : (nx∎ : D) → FUN! nx∎ ≡ nx∎
{-# ATP axiom funnyFV #-}

postulate
  -- Using a funny predicate name
  funnyP : (n : D) → PRED! n
{-# ATP axiom funnyP #-}

------------------------------------------------------------------------------
-- Testing a data constructor with holes.
data _×_ ( A B : Set) : Set where
  _,_ : A → B → A × B

data WithHoles : D × D → Set where
  withHoles : (x y : D) → WithHoles ( x , y )
{-# ATP hint withHoles #-}

------------------------------------------------------------------------------
-- We are only testing the translation of names, so we prove a tautology.
postulate
  t : (d : D) → d ≡ d
{-# ATP prove t #-}
