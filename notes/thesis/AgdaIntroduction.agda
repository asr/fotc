{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}
{-# OPTIONS --no-coverage-check #-}

module AgdaIntroduction where

-- Dependent function types
id : (A : Set) → A → A
id A x = x

-- λ-notation
id₂ : (A : Set) → A → A
id₂ = λ A → λ x → x

id₃ : (A : Set) → A → A
id₃ = λ A x → x

-- Implicit arguments
id₄ : {A : Set} → A → A
id₄ x = x

id₅ : {A : Set} → A → A
id₅ = λ x → x

-- Inductively defined sets and families
data Bool : Set where
  false true : Bool

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)

-- Structurally recursive functions and pattern matching
_+_ : ℕ → ℕ → ℕ
zero   + n = n
succ m + n = succ (m + n)

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- The absurd pattern
magic : {A : Set} → Fin zero → A
magic ()

-- The with constructor
filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs

filter' : {A : Set} → (A → Bool) → List A → List A
filter' p [] = []
filter' p (x ∷ xs) with p x
filter' p (x ∷ xs) | true  = x ∷ filter' p xs
filter' p (x ∷ xs) | false = filter' p xs

-- Mutual definitions
even : ℕ → Bool
odd  : ℕ → Bool

even zero     = true
even (succ n) = odd n

odd zero     = false
odd (succ n) = even n

data EvenList : Set
data OddList  : Set

data EvenList where
  []  : EvenList
  _∷_ : ℕ → OddList → EvenList

data OddList where
  _∷_ : ℕ → EvenList → OddList

-- Coverage and termination checkers
head : {A : Set} → List A → A
head (x ∷ xs) = x

ack : ℕ → ℕ → ℕ
ack zero     n        = succ n
ack (succ m) zero     = ack m (succ zero)
ack (succ m) (succ n) = ack m (ack (succ m) n)

{-# NO_TERMINATION_CHECK #-}
f : ℕ → ℕ
f n = f n

{-# NO_TERMINATION_CHECK #-}
nest : ℕ → ℕ
nest zero     = zero
nest (succ n) = nest (nest n)
