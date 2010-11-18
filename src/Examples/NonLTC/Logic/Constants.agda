------------------------------------------------------------------------------
-- Logical constants
------------------------------------------------------------------------------

module Examples.NonLTC.Logic.Constants where

-- The logical connectives

-- The logical connectives are hard-coded in our implementation,
-- i.e. the symbols ⊥, ⊤, ¬, ∧, ∨, →, and ↔ must be used.
open import Lib.Data.Empty       public using ( ⊥ )
open import Lib.Data.Product     public using ( _∧_ ; _,_ )
open import Lib.Data.Sum         public using ( _∨_ ; inj₁ ; inj₂ )
open import Lib.Data.Unit        public using ( ⊤ )
open import Lib.Relation.Nullary public using ( ¬_ )

infixr 2 _↔_

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) ∧ (Q → P)

-- The quantifiers

-- The universe of discourse.
open import LTC.Base.Core public using ( D )

-- In logic it is assumed that the universe of discourse is not empty.
postulate
  D≠∅ : D

-- The quantifiers are hard-coded in our implementation, i.e. the
-- symbols ∃D and ∀D (or →) must be used.

open import LTC.Data.Product public using ( _,_ ; ∃D )

