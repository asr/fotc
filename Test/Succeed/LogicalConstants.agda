module Test.Succeed.LogicalConstants where

infixr 4 _,_
infixr 2 _×_

postulate
  D     : Set
  equal : D → D → Set

------------------------------------------------------------------------------
-- The conjuction data type

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

-- Testing the conjunction data constructor
postulate
 testAndDataConstructor : {m n : D} →
                        (equal m m) →
                        (equal n n) →
                        (equal m m ) ∧ (equal n n)
{-# ATP prove testAndDataConstructor #-}

-- Testing the first projection
postulate
  testProj₁ : {m n : D} →
              (equal m m ) ∧ (equal n n) →
              (equal m m)
{-# ATP prove testProj₁ #-}

-- Testing the second projection
postulate
  testProj₂ : {m n : D} →
              (equal m m ) ∧ (equal n n) →
              (equal n n)
{-# ATP prove testProj₂ #-}
