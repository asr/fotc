------------------------------------------------------------------------------
-- Distributive groupoids base
------------------------------------------------------------------------------

module Draft.Groupoids.Base where

-- We add 3 to the fixities of the standard library.
-- infix  11 _⁻¹
infixl 10 _∙_

------------------------------------------------------------------------------

-- The groupoid universe
open import Common.Universe public renaming ( D to G )

-- The equality
-- The equality is the propositional identity on the groupoid universe.

-- N.B. The following modules are exported by this module.
open import Common.Relation.Binary.PropositionalEquality public
  using ( _≡_ ; refl )
open import Common.Relation.Binary.PropositionalEquality.Properties public
  using ( sym ; trans )

-- Distributive groupoids axioms

-- From: David Stanovsky. Distributive groupoids are
-- symmetrical-by-medial: An elementary proof. Commentations
-- Mathematicae Universitatis Carolinae, 49(4):541–546, 2008.
postulate
  _∙_ : G → G → G  -- The groupoid binary operation.

  leftDistributive  : ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ (x ∙ z)
  rightDistributive : ∀ x y z → (x ∙ y) ∙ z ≡ (x ∙ z) ∙ (y ∙ z)
{-# ATP axiom leftDistributive #-}
{-# ATP axiom rightDistributive #-}
