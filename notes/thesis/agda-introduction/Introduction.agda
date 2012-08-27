module Introduction where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (succ n)
  succ : {n : ℕ} → Fin n → Fin (succ n)
