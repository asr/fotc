------------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------------

module Lib.Data.Product where

infixr 4 _,_
infixr 2 _∧_

------------------------------------------------------------------------------
-- See LTC.Data.Product for the existential quantifier.

-- The conjunction data type.
-- It is not necessary to add the data constructor _,_ as an hint nor
-- strictly it is nececessary to define the projections ∧-proj₁ and
-- ∧-proj₂ because the ATPs implement them.
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

∧-proj₁ : {A B : Set} → A ∧ B → A
∧-proj₁ (x , y) = x

∧-proj₂ : {A B : Set} → A ∧ B → B
∧-proj₂ (x , y) = y
