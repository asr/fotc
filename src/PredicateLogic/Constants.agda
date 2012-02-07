------------------------------------------------------------------------------
-- Logical constants
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module PredicateLogic.Constants where

open import Common.Universe public using ( D )
open import Common.LogicalConstants public

infixr 3 _⇒_

------------------------------------------------------------------------------
-- We added extra symbols for the implication and the universal
-- quantification (see module Common.LogicalConstants).

-- Implication.
_⇒_ : Set → Set → Set
A ⇒ B = A → B

-- Universal quantification.
⋀ : (P : D → Set) → Set
⋀ P = (d : D) → P d
