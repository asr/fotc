------------------------------------------------------------------------------
-- Logical constants
------------------------------------------------------------------------------

module PredicateLogic.Constants where

open import Common.Universe public using ( D )
open import Common.LogicalConstants public

------------------------------------------------------------------------------
-- We added extra symbols for the implication and the universal
-- quantification (see module Common.LogicalConstants).

-- Implication
infixr 3 _⇒_
_⇒_ : Set → Set → Set
P ⇒ Q = P → Q

-- Universal quantification
⋀ : (P : D → Set) → Set
⋀ P = (d : D) → P d
