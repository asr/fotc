-- Issue: At the moment, we don't eta-expand the equations in the ATP
-- definitions.

module Issues.Eta where

postulate
  D       : Set
  binaryP : D → D → Set

data ∃ (P : D → Set) : Set where
  _,_ : (witness : D) → P witness → ∃ P

-- Because Agda eta-reduces the equations, the internal representation
-- of P corresponds to the function
--
-- P xs = ∃ (binary xs)
--
-- Due to it, we cannot proof the conjecture bar.

P : D → Set
P xs = ∃ λ ys → binaryP xs ys
{-# ATP definition P #-}

postulate
  foo : ∀ {xs} → (∃ λ ys → binaryP xs ys) → (∃ λ ys → binaryP xs ys)
{-# ATP prove foo #-}

postulate
  barP : ∀ {xs} → P xs → (∃ λ ys → binaryP xs ys)
{-# ATP prove bar #-}
