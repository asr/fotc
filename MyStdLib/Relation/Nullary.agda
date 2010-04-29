------------------------------------------------------------------------------
-- Operations on nullary relations
------------------------------------------------------------------------------

module MyStdLib.Relation.Nullary where

open import MyStdLib.Data.Empty

infix 3 ¬

------------------------------------------------------------------------------
-- Negation.

-- TODO: It is necessary an underscore (i.e. ¬_ ) (the standard
-- library uses it)?
¬ : Set → Set
¬ A = A → ⊥
