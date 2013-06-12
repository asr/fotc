{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Discussion about the inductive approach for representing
-- first-order theories.

-- Peter: If you take away the proof objects (as you do when you go to
-- predicate logic) the K axiom doesn't give you any extra power.

module ProofTerm where

infix 7  _≡_
infixr 7 _,_

postulate D : Set

-- The identity type on the universe of discourse.
data _≡_ (x : D) : D → Set where
  refl : x ≡ x

-- The existential quantifier type on D.
data ∃ (A : D → Set) : Set where
  _,_ : (t : D) → A t → ∃ A

foo : (∃ λ x → ∃ λ y → x ≡ y) → (∃ λ x → ∃ λ y → y ≡ x)
foo (x , .x , refl) = x , x , refl
