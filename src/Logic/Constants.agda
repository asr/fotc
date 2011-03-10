------------------------------------------------------------------------------
-- Logical constants
------------------------------------------------------------------------------

module Logic.Constants where

open import Common.Universe public using ( D )
open import Common.LogicalConstants public

------------------------------------------------------------------------------
-- We added extra symbols for the implication and the universal quantification.

-- Implication
infixr 3 _⇒_
_⇒_ : Set → Set → Set
P ⇒ Q = P → Q

-- Universal quantification
⋀ : (P : D → Set) → Set
⋀ P = (d : D) → P d

-- In logic it is assumed that the universe of discourse is not empty.
postulate
  D≠∅ : D
