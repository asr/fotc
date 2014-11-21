------------------------------------------------------------------------------
-- Comparing styles for equational reasoning
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOT.Common.FOL.Relation.Binary.PreorderReasoning.Comparison where

infix  7 _≡_
infixl 9  _+_

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

trans : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

postulate
  ℕ               : Set
  zero            : ℕ
  _+_             : ℕ → ℕ → ℕ
  +-comm          : (m n : ℕ) → m + n ≡ n + m
  +-rightIdentity : (n : ℕ) → n + zero ≡ n

module Thesis where
  -- From Ulf's thesis (p. 112).

  infix  7 _≃_
  infix  5 chain>_
  infixl 5 _===_by_
  infix  4 _qed

  data _≃_ (x y : ℕ) : Set where
    prf : x ≡ y → x ≃ y

  chain>_ : (x : ℕ) → x ≃ x
  chain> x = prf refl

  _===_by_ : {x y : ℕ} → x ≃ y → (z : ℕ) → y ≡ z → x ≃ z
  prf p === z by q = prf (trans {_} {_} {_} p q)

  _qed : {x y : ℕ} → x ≃ y → x ≡ y
  prf p qed = p

  -- Example.
  +-leftIdentity : (n : ℕ) → zero + n ≡ n
  +-leftIdentity n =
    chain> zero + n
       === n + zero by +-comm zero n
       === n        by +-rightIdentity n
    qed

module SL where
  -- Adapted from the Agda standard library 0.8.1 (see
  -- Relation/Binary/PreorderReasoning.agda).

  infix  7 _≃_
  infix  4 begin_
  infixr 5 _≡⟨_⟩_
  infix  5 _∎

  data _≃_ (x y : ℕ) : Set where
    prf : x ≡ y → x ≃ y

  begin_ : {x y : ℕ} → x ≃ y → x ≡ y
  begin prf x≡y = x≡y

  _≡⟨_⟩_ : (x : ℕ){y z : ℕ} → x ≡ y → y ≃ z → x ≃ z
  _ ≡⟨ x≡y ⟩ prf y≡z = prf (trans x≡y y≡z)

  _∎ : (x : ℕ) → x ≃ x
  _∎ _ = prf refl

  -- Example.
  +-leftIdentity : (n : ℕ) → zero + n ≡ n
  +-leftIdentity n =
    begin
      zero + n ≡⟨ +-comm zero n ⟩
      n + zero ≡⟨ +-rightIdentity n ⟩
      n
    ∎

module NonWrapper where
  -- A set of combinators without request a wrapper data type (Mu,
  -- S.-C., Ko, H.-S. and Jansson, P. (2009)).

  infixr 5 _≡⟨_⟩_
  infix  5 _∎

  _≡⟨_⟩_ : (x : ℕ){y z : ℕ} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : (x : ℕ) → x ≡ x
  _∎ _ = refl

  -- Example.
  +-leftIdentity : (n : ℕ) → zero + n ≡ n
  +-leftIdentity n = zero + n ≡⟨ +-comm zero n ⟩
                     n + zero ≡⟨ +-rightIdentity n ⟩
                     n        ∎

------------------------------------------------------------------------------
-- References
--
-- Mu, S.-C., Ko, H.-S. and Jansson, P. (2009). Algebra of programming
-- in Agda: Dependent types for relational program derivation. Journal
-- of Functional Programming 19.5, pp. 545–579.
