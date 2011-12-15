------------------------------------------------------------------------------
-- Logical constants
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module just exported all the logical constants. This module is
-- re-exported by (some) "base" modules.

module Common.LogicalConstants where

------------------------------------------------------------------------------
-- The propositional logical connectives

-- The logical connectives are hard-coded in our translation,
-- i.e. the symbols ⊥, ⊤, ¬, ∧, ∨, →, and ↔ must be used.
-- N.B. For the implication we use the Agda function type.
open import Common.Data.Empty public using ( ⊥ ; ⊥-elim )
open import Common.Data.Product public using ( _∧_ ; _,_ ; ∧-proj₁ ; ∧-proj₂ )
open import Common.Data.Sum public using ( _∨_ ; [_,_] ; inj₁ ; inj₂ )
open import Common.Data.Unit public using ( ⊤ )
open import Common.Relation.Nullary public using ( ¬_ )

infixr 2 _↔_

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) ∧ (Q → P)

------------------------------------------------------------------------------
-- The quantifiers

-- The existential quantifier
-- The existential quantifier is hard-coded in our translation,
-- i.e. the symbol ∃ must be used.

open import Common.Data.Product public using ( _,_ ; ∃ ; ∃-proj₁ ; ∃-proj₂ )

-- The universal quantifier
-- N.B. For the universal quantifier we use the Agda (dependent)
-- function type.
