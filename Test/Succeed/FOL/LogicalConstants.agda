------------------------------------------------------------------------------
-- Testing the translation of the logical constants
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Test.Succeed.FOL.LogicalConstants where

infix  5 ¬_
infixr 4 _∧_
infixr 3 _∨_
infixr 2 _⇒_
infixr 1 _↔_

------------------------------------------------------------------------------
-- Propositional logic

-- The logical constants

-- The logical constants are hard-coded in our implementation,
-- i.e. the following symbols must be used (it is possible to use Agda
-- non-dependent function space → instead of ⇒).
postulate
  ⊥ ⊤     : Set -- N.B. the name of the tautology symbol is "\top", not T.
  ¬_      : Set → Set -- N.B. the right hole.
  _∧_ _∨_ : Set → Set → Set
  _⇒_ _↔_ : Set → Set → Set

-- We postulate some formulae (which are translated as 0-ary
-- predicates).
postulate A B C : Set

-- The introduction and elimination rules for the propositional
-- connectives are theorems.
postulate
  →I  : (A → B) → A ⇒ B
  →E  : (A ⇒ B) → A → B
  ∧I  : A → B → A ∧ B
  ∧E₁ : A ∧ B → A
  ∧E₂ : A ∧ B → B
  ∨I₁ : A → A ∨ B
  ∨I₂ : B → A ∨ B
  ∨E  : (A ⇒ C) → (B ⇒ C) → A ∨ B → C
  ⊥E  : ⊥ → A
  ¬E : (¬ A → ⊥ ) → A
{-# ATP prove →I #-}
{-# ATP prove →E #-}
{-# ATP prove ∧I #-}
{-# ATP prove ∧E₁ #-}
{-# ATP prove ∧E₂ #-}
{-# ATP prove ∨I₁ #-}
{-# ATP prove ∨I₂ #-}
{-# ATP prove ∨E #-}
{-# ATP prove ⊥E #-}
{-# ATP prove ¬E #-}

-- Testing other logical constanst.
postulate
  thm₁ : A ∧ ⊤ → A
  thm₂ : A ∨ ⊥ → A
  thm₃ : A ↔ A
{-# ATP prove thm₁ #-}
{-# ATP prove thm₂ #-}
{-# ATP prove thm₃ #-}

------------------------------------------------------------------------------
-- Predicate logic

--- The universe of discourse.
postulate D : Set

-- The propositional equality is hard-coded in our implementation, i.e. the
-- following symbol must be used.
postulate _≡_ : D → D → Set

-- Testing propositional equality.
postulate refl : ∀ {x} → x ≡ x
{-# ATP prove refl #-}

-- The quantifiers are hard-coded in our implementation, i.e. the
-- following symbols must be used (it is possible to use Agda
-- dependent function space ∀ x → A instead of ⋀).
postulate
  ∃ : (A : D → Set) → Set
  ⋀ : (A : D → Set) → Set

-- We postulate some formulae and propositional functions.
postulate
  A⁰    : Set
  A¹ B¹ : D → Set
  A²    : D → D → Set

-- The introduction and elimination rules for the quantifiers are theorems.
postulate
  ∀I : ((x : D) → A¹ x) → ⋀ A¹
  ∀E : ⋀ A¹ → (t : D) → A¹ t
  -- This elimination rule cannot prove in Coq because in Coq we can
  -- have empty domains. We do not have this problem because the ATPs
  -- assume a non-empty domain.
  ∃I : ((t : D) → A¹ t) → ∃ A¹
  -- TODO: ∃E : (x : D) → ∃ A¹ → (A¹ x → B¹ x) → B¹ x
{-# ATP prove ∀I #-}
{-# ATP prove ∀E #-}
{-# ATP prove ∃I #-}
-- {-# ATP prove ∃E #-}
