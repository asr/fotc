------------------------------------------------------------------------------
-- Testing the translation of function, predicates and variables names
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From the technical manual of TPTP
-- (http://www.cs.miami.edu/~tptp/TPTP/TR/TPTPTR.shtml)

-- ... variables start with upper case letters, ... predicates and
-- functors either start with lower case and contain alphanumerics and
-- underscore ...

module Names where

infix 4 _≡_

------------------------------------------------------------------------------
-- Testing funny names

postulate
  D     : Set
  _≡_   : D → D → Set
  FUN!  : D → D   -- A funny function name.
  PRED! : D → Set -- A funny predicate name.

-- Using a funny function and variable name.
postulate funnyFV  : (nx∎ : D) → FUN! nx∎ ≡ nx∎
{-# ATP axiom funnyFV #-}

-- Using a funny predicate name.
postulate funnyP : (n : D) → PRED! n
{-# ATP axiom funnyP #-}

-- We need to have at least one conjecture to generate a TPTP file.
postulate refl : ∀ d → d ≡ d
{-# ATP prove refl #-}
