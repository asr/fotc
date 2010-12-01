------------------------------------------------------------------------------
-- Logical constants
------------------------------------------------------------------------------

module Logic.Constants where

open import Common.Universe public using ( D )
open import Common.LogicalConstants public

------------------------------------------------------------------------------
-- We added extra symbols for the implication and the universal quantification.

infixr 3 _⇒_
_⇒_ : Set → Set → Set
P ⇒ Q = P → Q

∀D : (P : D → Set) → Set
∀D P = (d : D) → P d

-- In logic it is assumed that the universe of discourse is not empty.
postulate
  D≠∅ : D
