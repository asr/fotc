module Test.Succeed.OnlyAxioms.DefinitionsInsideWhereClauses where

postulate
  D    : Set
  _≡_  : D → D → Set
  zero : D
  succ : D → D

-- Because the predicate P is inside a where clause, its translation
-- includes the bounded variables inside the where clause, i.e. its
-- translation must be ∀ x y. p(x,y) ↔ y = y.
test₁ : D → Set
test₁ d = P d
  where
    P : D → Set
    P a = a ≡ a
    {-# ATP definition P #-}

-- We need to remove the quantification over proofs from a definition
-- inside a where clause. The translation of P must be
--
-- ∀ x. n(x) → (∀ y. q(x, y) ↔ y = x),
--
-- i.e. we must erase the quantification on the variable Nn : N n.
data N : D → Set where
  zN : N zero
  sN : {n : D} → N n → N (succ n)

test₂ : {n : D} → N n → Set
test₂ {n} Nn = Q n
  where
    Q : D → Set
    Q m = m ≡ n
    {-# ATP definition Q #-}
