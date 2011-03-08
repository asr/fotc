------------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------------

module Common.Data.Product where

open import Common.Universe using ( D )

-- We add 3 to the fixities of the standard library.
infixr 6 _,_
infixr 5 _∧_

------------------------------------------------------------------------------
-- The conjunction data type.

-- It is not necessary to add the data constructor _,_ as an
-- (general/local) hint because the ATPs implement it.
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

-- It is not strictly necessary define the projections ∧-proj₁ and
-- ∧-proj₂ because the ATPs implement them. For the same reason, it is
-- not necessary to add them as (general/local) hints.
∧-proj₁ : {A B : Set} → A ∧ B → A
∧-proj₁ (x , y) = x

∧-proj₂ : {A B : Set} → A ∧ B → B
∧-proj₂ (x , y) = y

-- The existential quantifier type on D.
data ∃D (P : D → Set) : Set where
  _,_ : (witness : D) → P witness → ∃D P

∃D-proj₁ : {P : D → Set} → ∃D P → D
∃D-proj₁ (x , _) = x

∃D-proj₂ : {P : D → Set}(∃p : ∃D P) → P (∃D-proj₁ ∃p)
∃D-proj₂ (_ , px) = px
