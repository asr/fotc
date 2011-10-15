------------------------------------------------------------------------------
-- Testing various arguments in the ATP pragmas
------------------------------------------------------------------------------

module Test.Succeed.VariousArguments where

postulate
  D       : Set
  _≡_     : D → D → Set
  a b c d : D
  a≡b     : a ≡ b
  b≡c     : b ≡ c
  c≡d     : c ≡ d
{-# ATP axiom a≡b b≡c c≡d #-}

postulate a≡d : a ≡ d
{-# ATP prove a≡d #-}
