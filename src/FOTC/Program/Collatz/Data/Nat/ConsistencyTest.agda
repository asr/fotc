------------------------------------------------------------------------------
-- Test the consistency of FOTC.Program.Collatz.Data.Nat
------------------------------------------------------------------------------

-- In the module FOTC.Program.Collatz.Data.Nat we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Program.Collatz.Data.Nat.ConsistencyTest where

open import FOTC.Base

open import FOTC.Program.Collatz.Data.Nat

------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
