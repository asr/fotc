------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Definition08 where

postulate
  D    : Set
  _≡_  : D → D → Set
  P    : D → Set
  op   : D → D

-- In this case the proof term Pb is referenced in the types of the
-- definitions of c and d via the where clause. Therefore in the
-- translation of c and d, we need to erase this proof term.
foo : D → ∀ {b} → P b → D
foo a Pb = a
  where
  c : D
  c = a
  {-# ATP definition c #-}

  d : D
  d = op c
  {-# ATP definition d #-}

  postulate bar : d ≡ op a
  {-# ATP prove bar #-}
