------------------------------------------------------------------------------
-- Testing the translation of definitions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Definition07 where

postulate
  D   : Set
  _≡_ : D → D → Set
  P   : D → Set

-- We test the translation of a definition where we need to erase
-- proof terms.
foo : ∀ {a b} → P a → P b → D
foo {a} {b} Pa Pb = a
  where
  c : D
  c = a
  {-# ATP definition c #-}

  postulate bar : c ≡ a
  {-# ATP prove bar #-}
