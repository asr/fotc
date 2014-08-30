------------------------------------------------------------------------------
-- Problem with a simplified version of the combinators for preorder
-- reasoning
------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOT.Common.FOL.Relation.Binary.PreorderReasoning.ImplicitArgumentsProblem
  where

-- Nils suggested a possible problem with the relation

-- R : {A : Set} → A → A → Set
-- R _ _ = ⊤

-- and a version of the combinators for preorder reasoning without use
-- the wrapper data type. This example shows that Nils was right.

------------------------------------------------------------------------------

record ⊤ : Set where
  constructor tt

R : {A : Set} → A → A → Set
R _ _ = ⊤

R-refl : {A : Set}{x : A} → R x x
R-refl = tt

R-trans : {A : Set}{x y z : A} → R x y → R y z → R x z
R-trans _ _ = tt

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

module Thesis where
  -- From Ulf's thesis (p. 112).

  infix  7 _≃_
  infix  5 chain>_
  infixl 5 _===_by_
  infix  4 _qed

  data _≃_ {A : Set}(x y : A) : Set where
    prf : R x y → x ≃ y

  chain>_ : {A : Set}(x : A) → x ≃ x
  chain> x = prf (R-refl {x = x})

  _===_by_ : {A : Set}{x y : A} → x ≃ y → (z : A) → R y z → x ≃ z
  _===_by_ {x = x} {y} (prf p) z q = prf (R-trans {x = x} {y} {z} p q)

  _qed : {A : Set}{x y : A} → x ≃ y → R x y
  prf p qed = p

  -- Example (no problem with implicit arguments).
  test : (x y : ℕ) → R x y
  test x y =
    chain> x
      === y by tt
    qed

module SL where
  -- Adapted from the Agda standard library 0.6 (see
  -- Relation/Binary/PreorderReasoning.agda).

  infix  7 _≃_
  infix  4 begin_
  infixr 5 _≡⟨_⟩_
  infix  5 _∎

  data _≃_ {A : Set}(x y : A) : Set where
    prf : R x y → x ≃ y

  begin_ : {A : Set}{x y : A} → x ≃ y → R x y
  begin_ {x = x} (prf Rxy) = R-refl {x = x}

  _≡⟨_⟩_ : {A : Set}(x : A){y z : A} → R x y → y ≃ z → x ≃ z
  _≡⟨_⟩_ x {y} {z} Rxy (prf Ryz) = prf (R-trans {x = x} {y} {z} Rxy Ryz)

  _∎ : {A : Set}(x : A) → x ≃ x
  _∎ x = prf (R-refl {x = x})

  -- Example (no problem with implicit arguments).
  test : (x y : ℕ) → R x y
  test x y =
    begin
      x ≡⟨ tt ⟩
      y
    ∎

module NonWrapper where
  -- A set of combinators without request a wrapper data type (Mu,
  -- S.-C., Ko, H.-S. and Jansson, P. (2009)).

  infixr 5 _≡⟨_⟩_
  infix  5 _∎

  _≡⟨_⟩_ : {A : Set}(x : A){y z : A} → R x y → R y z → R x z
  _≡⟨_⟩_ x {y} {z} x≡y y≡z = R-trans {x = x} {y} {z} x≡y y≡z

  _∎ : {A : Set}(x : A) → R x x
  _∎ x = R-refl {x = x}

  -- Example.
  test : (x y : ℕ) → R x y
  test x y = x ≡⟨ tt ⟩
             y ∎

------------------------------------------------------------------------------
-- References
--
-- Mu, S.-C., Ko, H.-S. and Jansson, P. (2009). Algebra of programming
-- in Agda: Dependent types for relational program derivation. Journal
-- of Functional Programming 19.5, pp. 545–579.
