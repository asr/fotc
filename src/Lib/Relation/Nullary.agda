------------------------------------------------------------------------------
-- Operations on nullary relations
------------------------------------------------------------------------------

module Lib.Relation.Nullary where

open import Lib.Data.Empty using ( ⊥ )

infix 3 ¬_

------------------------------------------------------------------------------
-- Negation.
-- The underscore allows to write for example '¬ ¬ A' instead of '¬ (¬ A)'.
¬_ : Set → Set
¬ A = A → ⊥
