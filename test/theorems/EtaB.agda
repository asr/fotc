------------------------------------------------------------------------------
-- Testing the eta-expansion
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module EtaB where

postulate
  D  : Set
  P² : D → D → Set

data ∃ (A : D → Set) : Set where
  _,_ : (t : D) → A t → ∃ A

-- Because Agda eta-reduces the equations, the internal representation
-- of P corresponds to the predicate
--
-- P xs = ∃ (P² xs)
--
-- We eta-expand the definition of P before the translation to FOL.

P : D → Set
P xs = ∃ λ ys → P² xs ys
{-# ATP definition P #-}

postulate
  bar : ∀ {xs} → P xs → (∃ λ ys → P² xs ys)
{-# ATP prove bar #-}
