------------------------------------------------------------------------------
-- Test the consistency of FOTC.Program.Division.Division
------------------------------------------------------------------------------

-- In the module FOTC.Program.Division.Division we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module FOTC.Program.Division.Division.ConsistencyTest where

open import FOTC.Base

open import FOTC.Program.Division.Division

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
