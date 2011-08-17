------------------------------------------------------------------------------
-- Test the consistency of Draft.FOTC.Program.ABP.ABP
------------------------------------------------------------------------------

-- In the module Draft.FOTC.Program.ABP.ABP we declare Agda postulates
-- as FOL axioms. We test if it is possible to prove an unprovable
-- theorem from these axioms.

module Draft.FOTC.Program.ABP.ABP.ConsistencyTest where

open import FOTC.Base

open import Draft.FOTC.Program.ABP.ABP

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
