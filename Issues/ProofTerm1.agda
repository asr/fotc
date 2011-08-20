module Issues.ProofTerm1 where

postulate
  D   : Set
  _≡_ : D → D → Set
  P   : D → Set
  Q   : D → D → Set

foo : ∀ {a b} → P b → Q b b → D
foo {a} {b} Pb Qbb = a
  where
  c : D
  c = a
  {-# ATP definition c #-}

  postulate bar : c ≡ a
  {-# ATP prove bar #-}
