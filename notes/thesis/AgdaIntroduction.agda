{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}
{-# OPTIONS --no-coverage-check #-}

module AgdaIntroduction where

infixr 5 _∷_ _++_
infix  4 _≡_

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

{-# BUILTIN NATURAL ℕ     #-}
{-# BUILTIN ZERO    zero  #-}
{-# BUILTIN SUC     succ  #-}

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)

-- Structurally recursive functions and pattern matching
_+_ : ℕ → ℕ → ℕ
0      + n = n
succ m + n = succ (m + n)

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

f : ℕ → ℕ
f 0 = 0
f _ = 1

-- The absurd pattern
magic : {A : Set} → Fin 0 → A
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

even 0        = true
even (succ n) = odd n

odd 0        = false
odd (succ n) = even n

data EvenList : Set
data OddList  : Set

data EvenList where
  []  : EvenList
  _∷_ : ℕ → OddList → EvenList

data OddList where
  _∷_ : ℕ → EvenList → OddList

-- Normalisation

data _≡_ {A : Set}: A → A → Set where
  refl : {a : A} → a ≡ a

length : {A : Set} → List A → ℕ
length []       = 0
length (x ∷ xs) = 1 + length xs

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

succCong : {m n : ℕ} → m ≡ n → succ m ≡ succ n
succCong refl = refl

thm : {A : Set}(xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
thm [] ys       = refl
thm (x ∷ xs) ys = succCong (thm xs ys)

-- Coverage and termination checkers
head : {A : Set} → List A → A
head (x ∷ xs) = x

ack : ℕ → ℕ → ℕ
ack 0        n        = succ n
ack (succ m) 0        = ack m 1
ack (succ m) (succ n) = ack m (ack (succ m) n)

-- Combinators for equational reasoning

postulate
  sym   : {A : Set}{a b : A} → a ≡ b → b ≡ a
  trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
  subst : {A : Set}(P : A → Set){a b : A} → a ≡ b → P a → P b

postulate
  _*_             : ℕ → ℕ → ℕ
  *-comm          : ∀ m n → m * n ≡ n * m
  *-rightIdentity : ∀ n → n * 1 ≡ n

*-leftIdentity : ∀ n → 1 * n ≡ n
*-leftIdentity n =
  trans {ℕ} {1 * n} {n * 1} {n} (*-comm 1 n) (*-rightIdentity n)

module ER
  {A     : Set}
  (_∼_   : A → A → Set)
  (∼-refl  : ∀ {x} → x ∼ x)
  (∼-trans : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z)
  where

  infixr 5 _∼⟨_⟩_
  infix  5 _∎

  _∼⟨_⟩_ : ∀ x {y z} → x ∼ y → y ∼ z → x ∼ z
  _ ∼⟨ x∼y ⟩ y∼z = ∼-trans x∼y y∼z

  _∎ : ∀ x → x ∼ x
  _∎ _ = ∼-refl

open module ≡-Reasoning = ER _≡_ (refl {ℕ}) (trans {ℕ})
  renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )

*-leftIdentity' : ∀ n → 1 * n ≡ n
*-leftIdentity' n =
  1 * n ≡⟨ *-comm 1 n ⟩
  n * 1 ≡⟨ *-rightIdentity n ⟩
  n     ∎
