------------------------------------------------------------------------------
-- Formalization of Azcel's First-Order Theory of Combinators (FOTC) [*]

-- [*] Peter Aczel. The strength of Martin-Löf's intuitionistic type
-- theory with one universe. In S. Miettinen and J. Väänanen, editors,
-- Proc. of the Symposium on Mathematical Logic (Oulu, 1974), Report
-- No. 2, Department of Philosopy, University of Helsinki, Helsinki,
-- pages 1–32, 1977.

------------------------------------------------------------------------------

module Aczel-FOTC where

-- We add 3 to the fixities of the standard library.
infixl 9 _·_  -- The symbol is '\cdot'.
infix  7 _≡_

------------------------------------------------------------------------------

-- The universe.
postulate D : Set

-- The identity type on the universe of discourse.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

postulate
  K S : D
  _·_ : D → D → D

-- Conversion rules
postulate
  Kax : ∀ x y →       K · x · y ≡ x
  Sax : ∀ x y z → S · x · y · z ≡ x · z · (y · z)
