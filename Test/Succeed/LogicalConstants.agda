module Test.Succeed.LogicalConstants where

infix  4 _≡_

postulate
  D   : Set
  _≡_ : D → D → Set

------------------------------------------------------------------------------
-- The conjuction data type

module Conjunction where

  -- N.B. It is not necessary to define neither the data constructor
  -- _,_, nor the projections -- because the ATPs implement it.
  data _∧_ (A B : Set) : Set where

  -- Testing the data constructor and the projections.
  postulate
    A B     : Set
    _,_     : A → B → A ∧ B
    ∧-proj₁ : A ∧ B → A
    ∧-proj₂ : A ∧ B → B
  {-# ATP prove _,_ #-}
  {-# ATP prove ∧-proj₁ #-}
  {-# ATP prove ∧-proj₂ #-}

------------------------------------------------------------------------------
-- The negation

module Negation where

  infix 3 ¬

  data ⊥ : Set where

  ¬ : Set → Set
  ¬ A = A → ⊥

  postulate
    true false : D

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

  -- N.B. It is not necessary to define neither the data constructors
  -- inj₁ and inj₂ nor the disyunction elimination because the ATP
  -- implements them.
  data _∨_ (A B : Set) : Set where

  -- Testing the data constructors and the elimination.
  postulate
    A B C : Set
    inj₁  : A → A ∨ B
    inj₂  : B → A ∨ B
    [_,_] : (A → C) → (B → C) → A ∨ B → C
  {-# ATP prove inj₁ #-}
  {-# ATP prove inj₂ #-}
  {-# ATP prove [_,_] #-}

------------------------------------------------------------------------------
-- The existential type of D

module ExistentialQuantifier where

  data ∃D (P : D → Set) : Set where

  postulate
    test : (d : D) → ∃D (λ e → e ≡ d)
  {-# ATP prove test #-}
