------------------------------------------------------------------------------
-- Test the consistency of FOTC.Data.Nat.Inequalities
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- In the module FOTC.Data.Nat.Inequalities we declare Agda postulates
-- as first-order logic axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Data.Nat.Inequalities.Consistency.Axioms where

open import FOTC.Base
open import FOTC.Data.Nat.Inequalities

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
