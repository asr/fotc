------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

module Issues.Definition where

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

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/AgdaLib/Syntax/DeBruijn.hs:98