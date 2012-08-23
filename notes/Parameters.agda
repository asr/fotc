module Parameters where

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- Error: The type of the constructor does not fit in the sort of the
-- datatype, since Set₁ is not less or equal than Set when checking
-- the constructor [] in the declaration of List₁
--
-- data List₁ : Set → Set where
--   []  : {A : Set} → List₁ A
--   _∷_ : {A : Set} → A → List₁ A → List₁ A

data List₁ : Set → Set₁ where
  []  : {A : Set} → List₁ A
  _∷_ : {A : Set} → A → List₁ A → List₁ A
