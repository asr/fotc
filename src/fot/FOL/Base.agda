------------------------------------------------------------------------------
-- First-order logic base
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOL.Base where

infixr 3 _⇒_

------------------------------------------------------------------------------
-- First-order logic (without equality).
open import Common.FOL.FOL public

------------------------------------------------------------------------------
-- We added extra symbols for the implication and the universal
-- quantification (see module Common.FOL.FOL).

-- Implication.
_⇒_ : Set → Set → Set
A ⇒ B = A → B

-- Universal quantification.
--
-- 2012-02-03: Not used by the current formalization, but it is
-- accepted by the Apia program.
--
-- ⋀ : (A : D → Set) → Set
-- ⋀ A = (d : D) → A d

------------------------------------------------------------------------------
-- In first-order logic it is assumed that the universe of discourse
-- is nonempty.
postulate D≢∅ : D

------------------------------------------------------------------------------
-- The ATPs work in classical logic, therefore we add the principle of
-- the exclude middle for prove some non-intuitionistic theorems. Note
-- that we do not need to add the postulate as an ATP axiom.

-- The principle of the excluded middle.
postulate pem : ∀ {A} → A ∨ ¬ A
