module Test.Succeed.OnlyAxioms.Definitions where

postulate
  D   : Set
  _≡_ : D → D → Set

-- A predicate definition.
P : D → D → Set
P d₁ d₂ = d₁ ≡ d₂
{-# ATP definition P #-}

-- A function definition.
postulate
  foo : D → D → D

oof : D → D → D
oof d₁ d₂ = foo d₂ d₁
{-# ATP definition oof #-}
