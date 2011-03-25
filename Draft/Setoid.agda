------------------------------------------------------------------------------
-- Using setoids to formalize the FOTC
------------------------------------------------------------------------------

module Setoid where

-- We add 3 to the fixities of the standard library.
infixl 9 _·_  -- The symbol is '\cdot'.
infix  7 _≐_

------------------------------------------------------------------------------

data D : Set where
  K S : D
  _·_ : D → D → D

data _≐_ : D → D → Set where
  refl  : ∀ x →                                       x ≐ x
  sym   : ∀ {x y} → x ≐ y →                           y ≐ x
  trans : ∀ {x y z} → x ≐ y → y ≐ z →                 x ≐ z
  cong  : ∀ {x₁ x₂ y₁ y₂} → x₁ ≐ x₂ → y₁ ≐ y₂ → x₁ · y₁ ≐ x₂ · y₂
  Kax   : ∀ x y →                            K · x · y  ≐ x
  Sax   : ∀ x y z →                      S · x · y · z  ≐ x · z · (y · z)

-- It seems we cannot define the identity elimination using the setoid
-- equality
subst : ∀ {x y} (P : D → Set) → x ≐ y → P x → P y
subst P x≐y Px = {!!}
