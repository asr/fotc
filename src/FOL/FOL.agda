------------------------------------------------------------------------------
-- FOL (without equality)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module exported all the logical constants and the
-- propositional equality. This module is re-exported by the "base"
-- modules whose theories are defined on FOL (without equality)

module FOL.FOL where

------------------------------------------------------------------------------
-- The propositional logical connectives

-- The logical connectives are hard-coded in our translation,
-- i.e. the symbols ⊥, ⊤, ¬, ∧, ∨, →, and ↔ must be used.
-- N.B. For the implication we use the Agda function type.
open import FOL.Data.Empty public using ( ⊥ ; ⊥-elim )
open import FOL.Data.Product public using ( _∧_ ; _,_ ; ∧-proj₁ ; ∧-proj₂ )
open import FOL.Data.Sum public using ( _∨_ ; [_,_] ; inj₁ ; inj₂ )
open import FOL.Data.Unit public using ( ⊤ )
open import FOL.Relation.Nullary public using ( ¬_ )

infixr 2 _↔_

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) ∧ (Q → P)

------------------------------------------------------------------------------
-- The quantifiers

-- The existential quantifier
-- The existential quantifier is hard-coded in our translation,
-- i.e. the symbol ∃ must be used.

open import FOL.Data.Product public using ( ∃ ; ∃-elim ; ∃-intro )

-- The universal quantifier
-- N.B. For the universal quantifier we use the Agda (dependent)
-- function type.
