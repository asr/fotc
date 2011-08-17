------------------------------------------------------------------------------
-- Test the consistency of FOTC.Program.Mirror.Mirror
------------------------------------------------------------------------------

-- In the module FOTC.Program.Mirror.Mirror we declare Agda postulates
-- as FOL axioms. We test if it is possible to prove an unprovable
-- theorem from these axioms.

module FOTC.Program.Mirror.Mirror.ConsistencyTest where

open import FOTC.Base

open import FOTC.Program.Mirror.Mirror

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
