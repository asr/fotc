------------------------------------------------------------------------------
-- Test the consistency of FOTC.Program.GCD.GCD
------------------------------------------------------------------------------

-- In the module FOTC.Program.GCD.GCD we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module FOTC.Program.GCD.GCD.ConsistencyTest where

open import FOTC.Base

open import FOTC.Program.GCD.GCD

------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
