------------------------------------------------------------------------------
-- The identity type
------------------------------------------------------------------------------

-- Tested with the development version of Agda on 02 March 2012.

-- We can prove the properties of equality used in the formalization
-- of FOTC, from refl and J.

module IdentityType where

infix 7 _≡_

postulate
  D    : Set
  _≡_  : D → D → Set
  refl : ∀ {x} → x ≡ x

module TypeTheory where

  -- Using the type-theoretic eliminator for equality.

  postulate
    J : (C : ∀ x y → x ≡ y → Set) →
        (∀ x → (C x x refl)) →
        ∀ x y → (c : x ≡ y) → C x y c

  -- From Thorsten's slides: A short history of equality.
  sym : ∀ {x y} → x ≡ y → y ≡ x
  sym {x} {y} = J (λ x' y' _ → y' ≡ x') (λ x' → refl) x y

  -- From Thorsten's slides: A short history of equality.
  trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans {x} {y} {z} = J (λ x' y' _ → y' ≡ z → x' ≡ z) (λ x' pr → pr) x y

  subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
  subst A {x} {y} x≡y = J (λ x' y' _ → A x' → A y') (λ x' pr → pr) x y x≡y

module FOL where

  -- Using the usual elimination schema for predicate logic.

  postulate
    J : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y

  sym : ∀ {x y} → x ≡ y → y ≡ x
  sym {x} {y} x≡y = J (λ y' → y' ≡ x) x≡y refl

  trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans {x} {y} {z} x≡y = J (λ y' → y' ≡ z → x ≡ z) x≡y (λ pr → pr)

  subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
  subst = J

module ML where

  -- Using Martin-Löf elimination ("Hauptsatz ...", 1971).

  postulate
    J  : (C : D → D → Set) →
         (∀ x → (C x x)) →
         ∀ x y → x ≡ y → C x y

  sym : ∀ {x y} → x ≡ y → y ≡ x
  sym {x} {y} = J (λ x' y' → y' ≡ x') (λ x' → refl) x y

  trans : ∀ {x y z} → x ≡ y → y ≡ z → x ≡ z
  trans {x} {y} {z} = J (λ x' y' → y' ≡ z → x' ≡ z) (λ x' pr → pr) x y

  subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
  subst A {x} {y} x≡y = J (λ x' y' → A x' → A y') (λ x' pr → pr) x y x≡y
