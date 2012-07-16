------------------------------------------------------------------------------
-- Testing the eta-expansion
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module EtaC where

infix 7 _≡_
infixl 10 _*_

postulate
  D         : Set
  zero      : D
  _≡_       : D → D → Set
  _+_       : D → D → D
  lam       : (D → D) → D
  rec       : D → D → D → D
  *-helper₂ : D → D → D


-- We don't eta-expand the definition of _*_ before the translation,
-- because we cannot translate the lambda abstractions generated (from
-- *-helper₂ n ) to FOL terms.
_*_ : D → D → D
m * n = rec m zero (lam (*-helper₂ n))
{-# ATP definition _*_ #-}

postulate
  foo : ∀ n → n * n ≡ n * n
{-# ATP prove foo #-}
