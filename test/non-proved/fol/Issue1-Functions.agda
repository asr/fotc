{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From the technical manual of TPTP
-- (http://www.cs.miami.edu/~tptp/TPTP/TR/TPTPTR.shtml)

-- ... variables start with upper case letters, ... predicates and
-- functors either start with lower case and contain alphanumerics and
-- underscore ...

module Issue1-Functions where

postulate
  D : Set
  NAME : D → Set
  nAME : D → Set

postulate foo : ∀ a → NAME a
{-# ATP axiom foo #-}

-- This conjecture should not be proved.
postulate bar : ∀ a → nAME a
{-# ATP prove bar #-}
