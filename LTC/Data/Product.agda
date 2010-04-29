------------------------------------------------------------------------------
-- The existential quantifier type on D
------------------------------------------------------------------------------

module LTC.Data.Product where

open import LTC.Minimal.Core
-- open import MyStdLib.Data.Product

------------------------------------------------------------------------------
infixr 4 _,_

-- ∃D : (D → Set) → Set
-- ∃D P = ∃ P

data ∃D (P : D → Set) : Set where
  _,_ : (d : D) (Pd : P d) → ∃D P
