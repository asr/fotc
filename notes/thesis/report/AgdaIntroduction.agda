{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-coverage-check        #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module AgdaIntroduction where

-- We add 3 to the fixities of the Agda standard library 0.8.1 (see
-- Data/Nat.agda).
infixl 10 _*_
infixl 9  _+_
infixr 5  _∷_ _++_
infix  4  _≡_

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

f : ℕ → ℕ
f zero = zero
{-# CATCHALL #-}
f _    = succ zero

-- The absurd pattern
magic : {A : Set} → Fin zero → A
magic ()

-- The with constructor
--
-- 25 June 2014. Requires the TERMINATING flag when using
-- --without-K. See Agda issue 1214.

{-# TERMINATING #-}
filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
... | true  = x ∷ filter p xs
... | false = filter p xs

-- 24 June 2014. Requires the TERMINATING flag when using
-- --without-K. See Agda issue 1214.

{-# TERMINATING #-}
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

odd zero   = false
odd (succ n) = even n

data EvenList : Set
data OddList  : Set

data EvenList where
  []  : EvenList
  _∷_ : ℕ → OddList → EvenList

data OddList where
  _∷_ : ℕ → EvenList → OddList

-- Normalisation

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

length : {A : Set} → List A → ℕ
length []       = zero
length (x ∷ xs) = succ zero + length xs

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

succCong : {m n : ℕ} → m ≡ n → succ m ≡ succ n
succCong refl = refl

length-++ : {A : Set}(xs ys : List A) →
            length (xs ++ ys) ≡ length xs + length ys
length-++ [] ys       = refl
length-++ (x ∷ xs) ys = succCong (length-++ xs ys)

-- Coverage and termination checkers
head : {A : Set} → List A → A
head (x ∷ xs) = x

ack : ℕ → ℕ → ℕ
ack zero     n        = succ n
ack (succ m) zero     = ack m (succ zero)
ack (succ m) (succ n) = ack m (ack (succ m) n)

-- Combinators for equational reasoning

postulate
  sym   : {A : Set}{a b : A} → a ≡ b → b ≡ a
  trans : {A : Set}{a b c : A} → a ≡ b → b ≡ c → a ≡ c
  subst : {A : Set}(P : A → Set){a b : A} → a ≡ b → P a → P b

postulate
  _*_             : ℕ → ℕ → ℕ
  *-comm          : ∀ m n → m * n ≡ n * m
  *-rightIdentity : ∀ n → n * succ zero ≡ n

*-leftIdentity : ∀ n → succ zero * n ≡ n
*-leftIdentity n =
  trans {ℕ} {succ zero * n} {n * succ zero} {n} (*-comm (succ zero) n) (*-rightIdentity n)

module ER
  {A     : Set}
  (_∼_   : A → A → Set)
  (∼-refl  : ∀ {x} → x ∼ x)
  (∼-trans : ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z)
  where

  infixr 5 _∼⟨_⟩_
  infix  6 _∎

  _∼⟨_⟩_ : ∀ x {y z} → x ∼ y → y ∼ z → x ∼ z
  _ ∼⟨ x∼y ⟩ y∼z = ∼-trans x∼y y∼z

  _∎ : ∀ x → x ∼ x
  _∎ _ = ∼-refl

open module ≡-Reasoning = ER _≡_ (refl {ℕ}) (trans {ℕ})
  renaming ( _∼⟨_⟩_ to _≡⟨_⟩_ )

*-leftIdentity' : ∀ n → succ zero * n ≡ n
*-leftIdentity' n =
  succ zero * n ≡⟨ *-comm (succ zero) n ⟩
  n * succ zero ≡⟨ *-rightIdentity n ⟩
  n             ∎
