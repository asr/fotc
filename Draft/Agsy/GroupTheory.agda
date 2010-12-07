module GroupTheory where

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- We add 3 to the fixities of the standard library.
infix  11 _⁻¹
infixl 10 _∙_

------------------------------------------------------------------------------
-- Group theory axioms
postulate
  G   : Set        -- The group universe.
  ε   : G          -- The identity element.
  _∙_ : G → G → G  -- The group binary operation.
  _⁻¹ : G → G      -- The inverse function.

  associativity : (x y z : G) → x ∙ y ∙ z    ≡ x ∙ (y ∙ z)
  leftIdentity  : (x : G)     →     ε ∙ x    ≡ x
  rightIdentity : (x : G)     →     x ∙ ε    ≡ x
  leftInverse   : (x : G)     →  x ⁻¹ ∙ x    ≡ ε
  rightInverse  : (x : G)     →  x    ∙ x ⁻¹ ≡ ε

-- Properties

leftCancellation : (x y z : G) → x ∙ y ≡ x ∙ z → y ≡ z
leftCancellation x y z x∙y≡x∙z = {!-t 20 -m!}  -- Agsy fails
