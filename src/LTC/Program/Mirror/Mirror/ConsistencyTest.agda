------------------------------------------------------------------------------
-- Test the consistency of LTC.Program.Mirror.Mirror
------------------------------------------------------------------------------

-- In the module LTC.Program.Mirror.Mirror we declare Agda postulates
-- as FOL axioms. We test if it is possible to prove an unprovable
-- theorem from these axioms.

module LTC.Program.Mirror.Mirror.ConsistencyTest where

open import LTC.Base

open import LTC.Program.Mirror.Mirror

------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
