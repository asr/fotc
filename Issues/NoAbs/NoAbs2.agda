-- 20 June 2012. Agda is using (Pi _ (NoAbs _ _)) for the non-dependent
-- functions, so we have some bugs in the translation.

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Issues.NoAbs.NoAbs2 where

-- Test name: VariableNamesClash

infix  4 _≡_

postulate
  D   : Set
  _≡_ : D → D → Set
  a b : D

postulate a≡b : a ≡ b
{-# ATP axiom a≡b #-}

foo : (n : D) → a ≡ b
foo n = prf n
  where
  -- The translation of this postulate must use two diferents
  -- quantified variables names e.g. ∀ x. ∀ y. a ≡ b.
  postulate prf : (n : D) → a ≡ b
  {-# ATP prove prf #-}
