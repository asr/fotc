------------------------------------------------------------------------------
-- Discussion about the inductive approach
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Andrés: From our discussion about the inductive approach, can I
-- conclude that it is possible to rewrite the proofs using pattern
-- matching on _≡_, by proofs using only subst, because the types
-- associated with these proofs haven't proof terms?

-- Peter: Yes, provided the RHS of the definition does not refer to the
-- function defined, i e, there is no recursion.

module FOT.FOTC.InductiveApproach.Recursion where

open import FOTC.Base
open import FOTC.Data.Nat

------------------------------------------------------------------------------

foo : ∀ {m n} → m ≡ n → m + n ≡ m + m
foo refl = refl
