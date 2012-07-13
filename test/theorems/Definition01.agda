------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Definition01 where

postulate
  D   : Set
  _≡_ : D → D → Set
  d   : D

-- We test the translation of the definition of a 0-ary function.
e : D
e = d
{-# ATP definition e #-}

postulate foo : e ≡ d
{-# ATP prove foo #-}
