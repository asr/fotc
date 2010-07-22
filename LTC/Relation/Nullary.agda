------------------------------------------------------------------------------
-- Operations on nullary relations
------------------------------------------------------------------------------

module LTC.Relation.Nullary where

open import LTC.Data.Empty

infix 3 ¬_

------------------------------------------------------------------------------
-- Negation.
-- The underscore allows to write for example '¬ ¬ A' instead of '¬ (¬ A)'.
¬_ : Set → Set
¬ A = A → ⊥
