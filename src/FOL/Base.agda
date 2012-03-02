------------------------------------------------------------------------------
-- FOL base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOL.Base where

infixr 3 _⇒_

------------------------------------------------------------------------------
-- FOL (without equality).
open import Common.FOL.FOL public

------------------------------------------------------------------------------
-- We added extra symbols for the implication and the universal
-- quantification (see module FOL.FOL).

-- Implication.
_⇒_ : Set → Set → Set
A ⇒ B = A → B

-- Universal quantification.
--
-- 2012-02-03: Not used by the current formalization, but it is
-- accepted by the agda2atp program.
-- ⋀ : (A : D → Set) → Set
-- ⋀ A = (d : D) → A d

------------------------------------------------------------------------------
-- In FOL it is assumed that the universe of discourse is nonempty.
postulate D≠∅ : D

------------------------------------------------------------------------------
-- The ATPs work in classical logic, therefore we add the principle of
-- the exclude middle for prove some non-intuitionistic theorems.

-- The principle of the excluded middle.
postulate pem : ∀ {A} → A ∨ ¬ A
