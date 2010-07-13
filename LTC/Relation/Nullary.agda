------------------------------------------------------------------------------
-- Operations on nullary relations
------------------------------------------------------------------------------

module LTC.Relation.Nullary where

open import LTC.Data.Empty

infix 3 ¬

------------------------------------------------------------------------------
-- Negation.

-- TODO: It is necessary an underscore (i.e. ¬_ ) (the standard
-- library uses it)?
¬ : Set → Set
¬ A = A → ⊥
