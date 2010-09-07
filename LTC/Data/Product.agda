------------------------------------------------------------------------------
-- The product data type
------------------------------------------------------------------------------

module LTC.Data.Product where

open import LTC.Minimal.Core using ( D )

infixr 4 _,_
infixr 2 _∧_

------------------------------------------------------------------------------

-- ∃D : (D → Set) → Set
-- ∃D P = ∃ P

-- The existential quantifier type on D.
data ∃D (P : D → Set) : Set where
  _,_ : (d : D) (Pd : P d) → ∃D P

∃D-proj₁ : {P : D → Set} → ∃D P → D
∃D-proj₁ (x , _ ) = x

∃D-proj₂ : {P : D → Set} → (x-px : ∃D P) → P (∃D-proj₁ x-px)
∃D-proj₂ (_ , px) = px

-- The conjunction data type.
-- N.B. It is not necessary to add the data constructor _,_ as an hint
-- nor strictly it is nececessary to define the projections ∧-proj₁
-- and ∧-proj₂ because the ATPs implement them.
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

∧-proj₁ : {A B : Set} → A ∧ B → A
∧-proj₁ (x , y) = x

∧-proj₂ : {A B : Set} → A ∧ B → B
∧-proj₂ (x , y) = y
