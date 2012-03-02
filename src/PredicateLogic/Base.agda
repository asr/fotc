------------------------------------------------------------------------------
-- Predicate logic base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PredicateLogic.Base where

infixr 3 _⇒_

------------------------------------------------------------------------------

-- FOL (without equality).
open import Common.FOL.FOL public

-- We added extra symbols for the implication and the universal
-- quantification (see module FOL.FOL).

-- Implication.
_⇒_ : Set → Set → Set
A ⇒ B = A → B

-- Universal quantification.
⋀ : (P : D → Set) → Set
⋀ P = (d : D) → P d

-- In predicate logic it is assumed that the universe of discourse is
-- nonempty.
postulate D≠∅ : D
