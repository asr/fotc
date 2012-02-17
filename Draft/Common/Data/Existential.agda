-----------------------------------------------------------------------------
-- Existential elimination
-----------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of Agda on 16 February 2012.

module Existential where

-----------------------------------------------------------------------------

postulate
  D : Set

module ∃₁ where

  -- We add 3 to the fixities of the standard library.
  infixr 7 _,_

  -- The existential quantifier type on D.
  data ∃ (P : D → Set) : Set where
    _,_ : (x : D) → P x → ∃ P

  -- FOL existential elimination
  --     ∃x.P(x)   P(x) → Q
  --  ------------------------
  --             Q
  ∃-elim : {P : D → Set}{Q : Set} → ∃ P → ((x : D) → P x → Q) → Q
  ∃-elim (x , p) h = h x p

  -- Type theory existential elimination.
  ∃-proj₁ : ∀ {P} → ∃ P → D
  ∃-proj₁ (x , _) = x

  ∃-proj₂ : ∀ {P} → (p : ∃ P) → P (∃-proj₁ p)
  ∃-proj₂ (_ , Px) = Px

-----------------------------------------------------------------------------

module ∃₂ where
  -- A different version from the FOL existential introduction
  --     P(x)
  --  ------------
  --     ∃x.P(x)

  -- The existential quantifier type on D.
  data ∃ (P : D → Set) : Set where
    ∃-intro : ((x : D) → P x) → ∃ P

  postulate d : D

  -- FOL existential elimination.
  -- NB. It is neccesary that D ≠ ∅.
  ∃-elim : {P : D → Set}{Q : Set} → ∃ P → ((x : D) → P x → Q) → Q
  ∃-elim (∃-intro h₁) h₂ = h₂ d (h₁ d)
