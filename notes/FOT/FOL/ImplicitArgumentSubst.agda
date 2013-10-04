------------------------------------------------------------------------------
-- Testing subst using an implicit arguments for the propositional function.
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --schematic-propositional-functions #-}

module ImplicitArgumentSubst where

infix 7 _≡_

postulate
  D              : Set
  _·_            : D → D → D
  zero succ pred : D

succ₁ : D → D
succ₁ n = succ · n

pred₁ : D → D
pred₁ n = pred · n

-- The identity type on the universe of discourse.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- The propositional function is not an implicit argument.
subst : (A : D → Set) → ∀ {x y} → x ≡ y → A x → A y
subst A refl Ax = Ax

-- The propositional formula is an implicit argument.
subst' : {A : D → Set} → ∀ {x y} → x ≡ y → A x → A y
subst' refl Ax = Ax

sym : ∀ {x y} → x ≡ y → y ≡ x
sym refl = refl

-- Conversion rules.
postulate
  pred-0 : pred₁ zero            ≡ zero
  pred-S : ∀ n → pred₁ (succ₁ n) ≡ n

-- The FOTC natural numbers type.
data N : D → Set where
  nzero :               N zero
  nsucc : ∀ {n} → N n → N (succ₁ n)

-- Works using subst.
pred-N : ∀ {n} → N n → N (pred₁ n)
pred-N nzero          = subst N (sym pred-0) nzero
pred-N (nsucc {n} Nn) = subst N (sym (pred-S n)) Nn

-- Fails using subst'.
pred-N' : ∀ {n} → N n → N (pred₁ n)
pred-N' nzero          = subst' (sym pred-0) nzero
pred-N' (nsucc {n} Nn) = subst' (sym (pred-S n)) Nn
