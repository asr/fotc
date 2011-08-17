------------------------------------------------------------------------------
-- Testing the definition of functions
------------------------------------------------------------------------------

module Test.Succeed.DefinitionOfFunctions where

postulate
  D   : Set
  _≡_ : D → D → Set
  d   : D

e : D
e = d
{-# ATP definition e #-}

postulate
  foo : e ≡ d
{-# ATP prove foo #-}
