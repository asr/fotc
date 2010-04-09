module Test.Succeed.OnlyAxioms.Definitions where

postulate
  D   : Set
  _≡_ : D → D → Set

-- A predicate definition
P : D → D → Set
P d₁ d₂ = d₁ ≡ d₂
{-# ATP definition P #-}
