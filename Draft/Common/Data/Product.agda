-----------------------------------------------------------------------------
-- Existential elimination
-----------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Tested with the development version of Agda on 16 February 2012.

module Draft.Common.Data.Product where

-- We add 3 to the fixities of the standard library.
infixr 7 _,_

-----------------------------------------------------------------------------

postulate
  D : Set

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
