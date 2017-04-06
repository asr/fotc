------------------------------------------------------------------------------
-- Exclusive disjunction theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.ExclusiveDisjunction.TheoremsATP where

-- The theorems below are valid on intuitionistic logic and with an
-- empty domain.
open import FOL.Base hiding ( D≢∅ ; pem )
open import FOL.ExclusiveDisjunction.Base

------------------------------------------------------------------------------
-- We postulate some propositional formulae (which are translated as
-- 0-ary predicates).
postulate P Q : Set

-- We do not use the _⊻_ operator because its definition is not a
-- FOL-definition.

postulate
  p⊻q→p→¬q : ((P ∨ Q) ∧ ¬ (P ∧ Q)) → P → ¬ Q
{-# ATP prove p⊻q→p→¬q #-}

postulate
  p⊻q→q→¬p : ((P ∨ Q) ∧ ¬ (P ∧ Q)) → Q → ¬ P
{-# ATP prove p⊻q→q→¬p #-}

postulate
  p⊻q→¬p→q : ((P ∨ Q) ∧ ¬ (P ∧ Q)) → ¬ P → Q
{-# ATP prove p⊻q→¬p→q #-}

postulate
  p⊻q→¬q→p : ((P ∨ Q) ∧ ¬ (P ∧ Q)) → ¬ Q → P
{-# ATP prove p⊻q→¬q→p #-}

postulate
  ¬[p⊻q] : ¬ ((P ∨ Q) ∧ ¬ (P ∧ Q)) → ((P ∧ Q) ∨ (¬ P ∧ ¬ Q))
{-# ATP prove ¬[p⊻q] #-}
