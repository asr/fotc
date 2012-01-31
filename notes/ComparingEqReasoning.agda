------------------------------------------------------------------------------
-- Comparing styles for equational reasoning
------------------------------------------------------------------------------

module ComparingEqReasoning where

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

module Ulf where
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

  -- Example
  +-leftIdentity : (n : ℕ) → zero + n ≡ n
  +-leftIdentity n =
    chain> zero + n
       === n + zero by +-comm zero n
       === n        by +-rightIdentity n
    qed

module Nils where
  -- Adapted from the standard library (Relation.Binary.PreorderReasoning).

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

  -- A set of combinators without request a wrapper data type.

  -- From: Shin-Cheng Mu, Hsiang-Shang Ko, and Patrick
  -- Jansson. Algebra of programming in Agda: Dependent types for
  -- relational program derivation. Journal of Functional Programming,
  -- 19(5):545–579, 2009

  infixr 5 _≡⟨_⟩_
  infix  5 _∎

  _≡⟨_⟩_ : (x : ℕ){y z : ℕ} → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : (x : ℕ) → x ≡ x
  _∎ _ = refl

  +-leftIdentity : (n : ℕ) → zero + n ≡ n
  +-leftIdentity n =
    zero + n
      ≡⟨ +-comm zero n ⟩
    n + zero
      ≡⟨ +-rightIdentity n ⟩
    n ∎
