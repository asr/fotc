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
    P : D → Set

  -- Testing the conjunction data constructor
  postulate
    testAndDataConstructor : {m n : D} → P m → P n → P m ∧ P n
  {-# ATP prove testAndDataConstructor #-}

  -- Testing the first projection
  postulate
    testProj₁ : {m n : D} → P m ∧ P n → P m
  {-# ATP prove testProj₁ #-}

-- Testing the second projection
  postulate
    testProj₂ : {m n : D} → P m ∧ P n → P n
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
