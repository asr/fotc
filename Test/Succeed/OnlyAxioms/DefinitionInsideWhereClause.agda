module Test.Succeed.OnlyAxioms.DefinitionInsideWhereClause where

postulate
  D   : Set
  _≡_ : D → D → Set

-- Because the predicate P is inside a where clause, its translation
-- includes the binding variables inside the where clause, i.e. its
-- translation is ∀ x. ∀ y. p(x,y) ↔ y = y.
foo : D → Set
foo d = P d
  where
    P : D → Set
    P a = a ≡ a
    {-# ATP definition P #-}
