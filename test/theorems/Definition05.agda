------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Definition05 where

postulate
  D   : Set
  _≡_ : D → D → Set
  op  : D → D
  a   : D

b : D
b = a
{-# ATP definition b #-}

c : D
c = op b
{-# ATP definition c #-}

-- We test the use of an ATP definition inside other ATP definition.
postulate foo : c ≡ op a
{-# ATP prove foo #-}
