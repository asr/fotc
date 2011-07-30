-- Test for the eta-expansion of TPTP definitions.

module Issues.Eta2 where

infixl 10 _*_
infix 7 _≡_

postulate
  D         : Set
  zero      : D
  _≡_       : D → D → Set
  _+_       : D → D → D
  lam       : (D → D) → D
  rec       : D → D → D → D
  *-helper₂ : D → D → D

_*_ : D → D → D
m * n = rec m zero (lam (λ d → *-helper₂ n d))
{-# ATP definition _*_ #-}

postulate
  foo : ∀ n → n * n ≡ n * n
{-# ATP prove foo #-}
