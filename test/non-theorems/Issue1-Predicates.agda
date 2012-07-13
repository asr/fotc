{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From the technical manual of TPTP
-- (http://www.cs.miami.edu/~tptp/TPTP/TR/TPTPTR.shtml)

-- ... variables start with upper case letters, ... predicates and
-- functors either start with lower case and contain alphanumerics and
-- underscore ...

module Issue1-Predicates where

postulate
  D : Set
  a A : Set

-- This conjecture should not be proved.
postulate foo : a → A
{-# ATP prove foo #-}
