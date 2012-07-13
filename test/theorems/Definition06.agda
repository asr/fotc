------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Definition06 where

postulate
  D   : Set
  _≡_ : D → D → Set
  a c : D

b : D
b = a
{-# ATP definition b #-}

postulate
  foo : c ≡ b

-- We test the use of an ATP definition by a local hint.
postulate bar : c ≡ a
{-# ATP prove bar foo #-}
