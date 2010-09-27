-----------------------------------------------------------------------------
-- The sum (disjoint unions) data type
-----------------------------------------------------------------------------

module Lib.Data.Sum where

infixr 1 _∨_

-----------------------------------------------------------------------------
-- The disjunction data type.
-- It is not necessary to add the data constructors inj₁ and inj₂ as
-- hints nor strictly it is nececessary to define the eliminator [_,_]
-- because the ATPs implement them.
data _∨_ (A B : Set) : Set where
  inj₁ : (x : A) → A ∨ B
  inj₂ : (y : B) → A ∨ B

[_,_] : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y
