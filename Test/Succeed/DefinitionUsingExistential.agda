module Test.Succeed.DefinitionUsingExistential where

postulate
  D   : Set
  N   : D → Set
  _≡_ : D → D → Set

data ∃ (P : D → Set) : Set where
  _,_ : (witness : D) → P witness → ∃ P

------------------------------------------------------------------------------

foo : ∀ {n} → N n → D
foo {n} Nn = n
  where
  P : D → Set
  P d = ∃ λ e → e ≡ d
  {-# ATP definition P #-}

  postulate
    bar : ∀ {d} → P d → P d
  {-# ATP prove bar #-}
