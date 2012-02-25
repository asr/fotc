------------------------------------------------------------------------------
-- Products
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOL.Data.Product where

open import FOL.Universe using ( D )

-- We add 3 to the fixities of the standard library.
infixr 7 _,_ _,,_
infixr 5 _∧_

------------------------------------------------------------------------------
-- The conjunction data type.

-- It is not necessary to add the data constructor _,_ as an
-- axiom because the ATPs implement it.
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B

-- It is not strictly necessary define the projections ∧-proj₁ and
-- ∧-proj₂ because the ATPs implement them. For the same reason, it is
-- not necessary to add them as (general/local) hints.
∧-proj₁ : ∀ {A B} → A ∧ B → A
∧-proj₁ (x , _) = x

∧-proj₂ : ∀ {A B} → A ∧ B → B
∧-proj₂ (_ , y) = y

-- 2012-02-24: We are using a *temporal* notation for the data constructor.
-- TODO: To rename the data constructor!
-- The existential quantifier type on D.
data ∃ (P : D → Set) : Set where
  _,,_ : (x : D) → P x → ∃ P

-- Sugar syntax for the existential quantifier.
syntax ∃ (λ x → e) = ∃[ x ] e

-- The existential elimination.

-- NB. We do not use the usual type theory elimination with two
-- projections because we are working in first-order logic where we
-- cannot extract a term from an existence proof.
∃-elim : {P : D → Set}{Q : Set} → ∃ P → ((x : D) → P x → Q) → Q
∃-elim (x ,, p) h = h x p
