------------------------------------------------------------------------------
-- Test the consistency of LTC.Program.GCD.GCD
------------------------------------------------------------------------------

-- In the module LTC.Program.GCD.GCD we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module LTC.Program.GCD.GCD.ConsistencyTest where

open import LTC.Base

open import LTC.Program.GCD.GCD

------------------------------------------------------------------------------

postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
