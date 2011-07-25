------------------------------------------------------------------------------
-- Testing the removal of the quantification on proof terms
------------------------------------------------------------------------------

module Test.Succeed.EraseQuantificationOnProofTerms2 where

postulate
  D    : Set
  zero : D
  succ : D → D
  _≡_  : D → D → Set

data N : D → Set where
  zN : N zero
  sN : ∀ {n} → N n → N (succ n)

-- Because we are using a where clause, the type of bar is
--
-- bar : (n : D) → (Nn : N n) → (m : D) → m ≡ m
--
-- thefore, we must erase the quantification on the variable Nn : N n.
foo : ∀ n → N n → n ≡ n
foo n Nn = bar n
  where
  postulate bar : ∀ m → m ≡ m
  {-# ATP prove bar #-}
