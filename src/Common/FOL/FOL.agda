------------------------------------------------------------------------------
-- FOL (without equality)
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- This module is re-exported by the "base" modules whose theories are
-- defined on FOL (without equality).

-- The logical connectives are hard-coded in our translation,
-- i.e. the symbols ⊥, ⊤, ¬, ∧, ∨, →, and ↔ must be used.
--
-- N.B. For the implication we use the Agda function type.
--
-- N.B For the universal quantifier we use the Agda (dependent)
-- function type.

module Common.FOL.FOL where

-- We add 3 to the fixities of the Agda standard library.
infixr 7 _,_
infix  6 ¬_
infixr 5 _∧_
infixr 4 _∨_
infixr 2 _↔_

----------------------------------------------------------------------------
-- The universe of discourse/universal domain.
postulate D : Set

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
∧-proj₁ (a , _) = a

∧-proj₂ : ∀ {A B} → A ∧ B → B
∧-proj₂ (_ , b) = b

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
[_,_] : ∀ {A B} → {C : Set} → (A → C) → (B → C) → A ∨ B → C
[ f , g ] (inj₁ a) = f a
[ f , g ] (inj₂ b) = g b

------------------------------------------------------------------------------
-- The empty type.
data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

------------------------------------------------------------------------------
-- The unit type.
-- N.B. The name of this type is "\top", not T.
data ⊤ : Set where
  tt : ⊤

------------------------------------------------------------------------------
-- Negation.
-- The underscore allows to write for example '¬ ¬ A' instead of '¬ (¬ A)'.
¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------------
-- The biconditional.
_↔_ : Set → Set → Set
A ↔ B = (A → B) ∧ (B → A)

------------------------------------------------------------------------------
-- The existential quantifier type on D.
data ∃ (P : D → Set) : Set where
  ∃-intro : ∀ {x} → P x → ∃ P

-- Sugar syntax for the existential quantifier.
syntax ∃ (λ x → e) = ∃[ x ] e

-- The existential elimination.
--
-- NB. We do not use the usual type theory elimination with two
-- projections because we are working in first-order logic where we do
-- need extract a witness from an existence proof.
∃-elim : {P : D → Set}{Q : Set} → ∃ P → (∀ {x} → P x → Q) → Q
∃-elim (∃-intro Px) h = h Px
