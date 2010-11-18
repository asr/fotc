------------------------------------------------------------------------------
-- Logical constants
------------------------------------------------------------------------------

module Examples.NonLTC.LogicATP.Constants where

-- The logical connectives

-- The logical connectives are hard-coded in our implementation,
-- i.e. the symbols ⊥, ⊤, ¬, ∧, ∨, ⇒ (or →), and ↔ must be used.
open import Lib.Data.Empty       public using ( ⊥ )
open import Lib.Data.Product     public using ( _∧_ )
open import Lib.Data.Sum         public using ( _∨_ )
open import Lib.Data.Unit        public using ( ⊤ )
open import Lib.Relation.Nullary public using ( ¬_ )

infixr 3 _⇒_
infixr 2 _↔_

_⇒_ : Set → Set → Set
P ⇒ Q = P → Q

_↔_ : Set → Set → Set
P ↔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

-- The quantifiers

-- The universe of discourse.
open import LTC.Base.Core public using ( D )

-- The quantifiers are hard-coded in our implementation, i.e. the
-- symbols ∃D and ∀D (or →) must be used.

open import LTC.Data.Product public using ( ∃D )

∀D : (P : D → Set) → Set
∀D P = (d : D) → P d
