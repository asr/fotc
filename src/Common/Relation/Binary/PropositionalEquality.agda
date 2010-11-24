------------------------------------------------------------------------------
-- Propositional equality
------------------------------------------------------------------------------

module Common.Relation.Binary.PropositionalEquality where

open import Common.Universe using ( D )

infix  7 _≡_  -- We add 3 to the fixities of the standard library.

------------------------------------------------------------------------------
-- The identity type on the universe of discourse.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x
