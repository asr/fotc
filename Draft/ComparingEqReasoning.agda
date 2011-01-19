------------------------------------------------------------------------------
-- Comparing Ulf and Nils styles for equational reasoning
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

infix 7 _≃_

private
  data _≃_ (x y : ℕ) : Set where
    prf : x ≡ y → x ≃ y

module Ulf where
  -- Adapted from the Ulf's thesis (p. 112).

  infix  5 chain>_
  infixl 5 _===_by_
  infix  4 _qed

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

  infix  4 begin_
  infixr 5 _≡⟨_⟩_
  infix  5 _∎

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
