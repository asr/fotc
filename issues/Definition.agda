------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Definition where

postulate
  D   : Set
  _≡_ : D → D → Set
  P   : D → Set

-- We test the translation of a definition where we need to erase proof terms.
foo : ∀ {a} → P a → ∀ {b} → P b → D
foo {a} Pa {b} Pb = a
  where
  c : D
  c = a
  {-# ATP definition c #-}

  postulate bar : c ≡ a
  {-# ATP prove bar #-}

-- $ agda2atp Issues/Definition.agda
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/AgdaLib/DeBruijn.hs:127
