------------------------------------------------------------------------------
-- Distributive laws base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.Base where

-- We add 3 to the fixities of the standard library.
infixl 10 _·_  -- The symbol is '\cdot'.

------------------------------------------------------------------------------
-- FOL with equality.
-- NB. This is an equational theory, so we do not import the logical
-- constants.
open import Common.FOL.FOL-Eq public using ( _≡_ ; D ; refl ; subst ; sym )

-- Distributive laws axioms

postulate
  _·_ : D → D → D  -- The binary operation.

  leftDistributive  : ∀ x y z → x · (y · z) ≡ (x · y) · (x · z)
  rightDistributive : ∀ x y z → (x · y) · z ≡ (x · z) · (y · z)
{-# ATP axiom leftDistributive rightDistributive #-}
