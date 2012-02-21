------------------------------------------------------------------------------
-- Nonempty universe of discourse
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In predicate logic it is assumed that the universe of discourse is
-- nonempty.

module PredicateLogic.NonEmptyDomain where

open import FOL.Universe

------------------------------------------------------------------------------

postulate D≠∅ : D
