------------------------------------------------------------------------
-- Unary relations
------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Adapted from the standard library.

module Common.Relation.Unary where

-- We add 3 to the fixities of the standard library.
infix 7 _∈_ _⊆_

------------------------------------------------------------------------
-- Unary relations
Pred : Set → Set₁
Pred A = A → Set

_∈_ : ∀ {A} → A → Pred A → Set
x ∈ P = P x

-- P ⊆ Q means that P is a subset of Q.
_⊆_ : ∀ {A} → Pred A → Pred A → Set
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q
