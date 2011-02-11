-----------------------------------------------------------------------------
-- The sum (disjoint unions)
-----------------------------------------------------------------------------

module Common.Data.Sum where

-- We add 3 to the fixities of the standard library.
infixr 4 _∨_

-----------------------------------------------------------------------------
-- The disjunction data type.

-- It is not necessary to add the data constructors inj₁ and inj₂ as
-- (general/local) hints because the ATPs implement them (actually, it
-- will be yield an error in the translation by the agda2atp tool).
data _∨_ (A B : Set) : Set where
  inj₁ : (x : A) → A ∨ B
  inj₂ : (y : B) → A ∨ B

-- It is not strictly necessary define the eliminator [_,_] because
-- the ATPs implement it. For the same reason, it is not necessary to
-- add it as a (general/local) hint (actually, it will be yield an
-- error in the translation by the agda2atp tool).
[_,_] : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y
