------------------------------------------------------------------------------
-- Distributive laws base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _·_  -- The symbol is '\cdot'.

------------------------------------------------------------------------------

-- The universe
open import Common.Universe public

-- The equality
-- The equality is the propositional identity on the universe.
import Common.Relation.Binary.PropositionalEquality
open module Eq =
  Common.Relation.Binary.PropositionalEquality.Inductive public

-- Distributive laws axioms

postulate
  _·_ : D → D → D  -- The binary operation.

  leftDistributive  : ∀ x y z → x · (y · z) ≡ (x · y) · (x · z)
  rightDistributive : ∀ x y z → (x · y) · z ≡ (x · z) · (y · z)
{-# ATP axiom leftDistributive rightDistributive #-}
