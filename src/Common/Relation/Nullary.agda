------------------------------------------------------------------------------
-- Operations on nullary relations
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Common.Relation.Nullary where

open import Common.Data.Empty using ( ⊥ )

-- We add 3 to the fixities of the standard library.
infix 6 ¬_

------------------------------------------------------------------------------
-- Negation.
-- The underscore allows to write for example '¬ ¬ A' instead of '¬ (¬ A)'.
¬_ : Set → Set
¬ A = A → ⊥
