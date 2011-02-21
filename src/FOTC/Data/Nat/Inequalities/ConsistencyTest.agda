------------------------------------------------------------------------------
-- Test the consistency of FOTC.Data.Nat.Inequalities
------------------------------------------------------------------------------

-- In the module FOTC.Data.Nat.Inequalities we declare Agda postulates
-- as FOL axioms. We test if it is possible to prove an unprovable
-- theorem from these axioms.

module FOTC.Data.Nat.Inequalities.ConsistencyTest where

open import FOTC.Base

open import FOTC.Data.Nat.Inequalities
------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
