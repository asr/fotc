-----------------------------------------------------------------------------
-- The sum (disjoint unions)
-----------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Common.Data.Sum where

-- We add 3 to the fixities of the standard library.
infixr 4 _∨_

-----------------------------------------------------------------------------
-- The disjunction data type.

-- It is not necessary to add the data constructors inj₁ and inj₂ as
-- axioms because the ATPs implement them.
data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

-- It is not strictly necessary define the eliminator [_,_] because
-- the ATPs implement it. For the same reason, it is not necessary to
-- add it as a (general/local) hint.
[_,_] : ∀ {A B} {C : Set} → (A → C) → (B → C) → A ∨ B → C
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y
