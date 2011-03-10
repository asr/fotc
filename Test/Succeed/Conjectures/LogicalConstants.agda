module Test.Succeed.Conjectures.LogicalConstants where

infix  5 ¬_
infixr 4 _∧_
infixr 3 _∨_
infixr 2 _⇒_
infixr 1 _↔_

------------------------------------------------------------------------------
-- Propositional logic

-- The logical connectives

-- The logical connectives are hard-coded in our implementation,
-- i.e. the following symbols must be used.
postulate
  ⊥ ⊤     : Set -- N.B. the name of the tautology symbol is "\top", not T.
  ¬_      : Set → Set -- N.B. the right hole.
  _∧_ _∨_ : Set → Set → Set
  _⇒_ _↔_ : Set → Set → Set

-- We postulate some propositional variables (which are translated as
-- 0-ary predicates).
postulate
  P Q R : Set

-- The introduction and elimination rules for the propositional
-- connectives are theorems.
postulate
  →I  : (P → Q) → P ⇒ Q
  →E  : (P ⇒ Q) → P → Q
  ∧I  : P → Q → P ∧ Q
  ∧E₁ : P ∧ Q → P
  ∧E₂ : P ∧ Q → Q
  ∨I₁ : P → P ∨ Q
  ∨I₂ : Q → P ∨ Q
  ∨E  : (P ⇒ R) → (Q ⇒ R) → P ∨ Q → R
  ⊥E  : ⊥ → P
  ¬E : (¬ P → ⊥ ) → P
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

------------------------------------------------------------------------------
-- Predicate logic

-- The universe of discourse.
postulate
  D : Set

-- The quantifiers are hard-coded in our implementation, i.e. the
-- following symbols must be used.
postulate
  ∃ : (P : D → Set) → Set
  ⋀ : (P : D → Set) → Set

-- We postulate some predicate symbols.
postulate
  P⁰    : Set
  P¹ Q¹ : D → Set
  P²    : D → D → Set

-- The introduction and elimination rules for the quantifiers are theorems.
postulate
  ∀I : ((x : D) → P¹ x) → ⋀ P¹
  ∀E : ⋀ P¹ → (t : D) → P¹ t
  -- This elimination rule cannot prove in Coq because in Coq we can
  -- have empty domains. We do not have this problem because the ATPs
  -- assume a non-empty domain.
  ∃I : ((t : D) → P¹ t) → ∃ P¹
  -- TODO: ∃E : (x : D) → ∃ P¹ → (P¹ x → Q¹ x) → Q¹ x
{-# ATP prove ∀I #-}
{-# ATP prove ∀E #-}
{-# ATP prove ∃I #-}
-- {-# ATP prove ∃E #-}
