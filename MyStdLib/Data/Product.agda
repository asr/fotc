-----------------------------------------------------------------------------
-- The product data type
-----------------------------------------------------------------------------

module MyStdLib.Data.Product where

-- infixr 4 _,_
-- infixr 2 _×_

-- data Σ (A : Set) (B : A → Set) : Set where
--   _,_ : (x : A) (y : B x) → Σ A B

-- ∃ : {A : Set} → (A → Set) → Set
-- ∃ = Σ _

-- _×_ : (A B : Set) → Set
-- A × B = Σ A (λ _ → B)

-- data _×_ (A B : Set) : Set where
--   _,_ : A → B → A × B

-- ×-proj₁ : {A B : Set} → A × B → A
-- ×-proj₁ (x , y) = x

-- ×-proj₂ : {A B : Set} → A × B → B
-- ×-proj₂ (x , y) = y


-- N.B. It is not necessary to add the constructor _,_ , nor the fields
-- proj₁, proj₂ as hints, because the ATP implements them.

-- _∧_ : (A B : Set) → Set
-- A ∧ B = A × B

infixr 2 _∧_
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

∧-proj₁ : {A B : Set} → A ∧ B → A
∧-proj₁ (x , y) = x

∧-proj₂ : {A B : Set} → A ∧ B → B
∧-proj₂ (x , y) = y
