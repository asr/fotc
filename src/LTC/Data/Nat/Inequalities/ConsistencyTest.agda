------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.Nat.Inequalities
------------------------------------------------------------------------------

-- In the module LTC.Data.Nat.Inequalities we declare Agda postulates
-- as FOL axioms. We test if it is possible to prove an unprovable
-- theorem from these axioms.

module LTC.Data.Nat.Inequalities.ConsistencyTest where

open import LTC.Base

open import LTC.Data.Nat.Inequalities
------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
