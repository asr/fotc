module Test.Succeed.Conjectures.VariableNamesClash where

infix  4 _≡_

postulate
  D : Set
  _≡_ : D → D → Set
  a b : D

postulate a≡b : a ≡ b
{-# ATP axiom a≡b #-}

foo : (n : D) → a ≡ b
foo n = prf n
  where
  -- The translation of this postulate must use two diferents
  -- quantified variables names e.g. ∀ x. ∀ y. x ≡ y.
  postulate prf : (n : D) → a ≡ b
  {-# ATP prove prf #-}
