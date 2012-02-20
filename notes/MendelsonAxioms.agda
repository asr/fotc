-- Tested with the development version of Agda on 20 February 2012.

module MendelsonAxioms where

-- We add 3 to the fixities of the standard library.
infixl 10 _*_
infixl 9  _+_
infix 7   _≡_

postulate
  M       : Set
  zero    : M
  succ    : M → M
  _+_ _*_ : M → M → M

-- The identity type on the universe of discourse.
data _≡_ (x : M) : M → Set where
  refl : x ≡ x

-- Impossible.
-- S₄ : ∀ {m n} → succ m ≡ succ n → m ≡ n
-- S₄ h = {!!}
