------------------------------------------------------------------------------
-- Testing the eta-expansion
------------------------------------------------------------------------------

module Test.Succeed.Eta2 where

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
-- We eta-expand the definition of P before the translation to FOL.

P : D → Set
P xs = ∃ λ ys → binaryP xs ys
{-# ATP definition P #-}

postulate
  bar : ∀ {xs} → P xs → (∃ λ ys → binaryP xs ys)
{-# ATP prove bar #-}
