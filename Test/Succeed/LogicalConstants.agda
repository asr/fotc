module Test.Succeed.LogicalConstants where

infix  4 _≡_

postulate
  D   : Set
  _≡_ : D → D → Set

------------------------------------------------------------------------------
-- The conjuction data type

module Conjunction where

  infixr 4 _,_
  infixr 2 _×_

  -- We want to use the product type to define the conjunction type
  record _×_ (A B : Set) : Set where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B

  -- N.B. It is not necessary to add the constructor _,_, nor the fields
  -- proj₁, proj₂ as hints, because the ATP implements it.

  _∧_ : (A B : Set) → Set
  A ∧ B = A × B

  postulate
    P   : D → Set
    d e : D

  -- Testing the conjunction data constructor
  postulate
    testAndDataConstructor : P d → P e → P d ∧ P e
  {-# ATP prove testAndDataConstructor #-}

  -- Testing the first projection
  postulate
    testProj₁ : P d ∧ P e → P d
  {-# ATP prove testProj₁ #-}

  -- Testing the second projection
  postulate
    testProj₂ : P d ∧ P e → P e
  {-# ATP prove testProj₂ #-}

------------------------------------------------------------------------------
-- The negation

module Negation where

  infix 3 ¬

  data ⊥ : Set where

  ¬ : Set → Set
  ¬ A = A → ⊥

  postulate
    true  : D
    false : D

  postulate
    true≠false : ¬ (true ≡ false)
  {-# ATP axiom true≠false #-}

  postulate
    testContradiction : (d : D) → true ≡ false → d ≡ true
  {-# ATP prove testContradiction #-}

------------------------------------------------------------------------------
-- The disjunction data type

module Disjunction where
  infixr 1 _∨_

  -- N.B. It is not necessary to add the constructors inj₁ and inj₂
  -- nor the elimantion [_,_] as hints, because the ATP implements it.

  data _∨_ (A B : Set) : Set where
    inj₁ : (x : A) → A ∨ B
    inj₂ : (y : B) → A ∨ B

  [_,_] : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
  [ f , g ] (inj₁ x) = f x
  [ f , g ] (inj₂ y) = g y

  postulate
    P   : D → Set
    d e f : D

  -- Testing the disjunction data constructors
  postulate
    inj₁Or : P d → P d ∨ P e
    inj₂Or : P e → P d ∨ P e
  {-# ATP prove inj₁Or #-}
  {-# ATP prove inj₂Or #-}

  -- Testing the disjunction elimination
  postulate
    A : Set
    B : Set
    orElim :  (P d → P f) → (P e → P f) → P d ∨ P e → P f
  {-# ATP prove orElim #-}
