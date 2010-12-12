------------------------------------------------------------------------------
-- Test the consistency of AbelianGroupTheory.Base
------------------------------------------------------------------------------

-- In the module AbelianGroupTheory.Base we declare Agda postulates
-- as FOL axioms. We test if it is possible to prove an unprovable
-- theorem from these axioms.

module AbelianGroupTheory.Base.ConsistencyTest where

open import AbelianGroupTheory.Base

------------------------------------------------------------------------------

postulate
  impossible : (d e : G) → d ≡ e
{-# ATP prove impossible #-}
