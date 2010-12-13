------------------------------------------------------------------------------
-- Test the consistency of GroupTheory.Groupoids.Base
------------------------------------------------------------------------------

-- In the module GroupTheory.Groupoids.Base we declare Agda postulates
-- as FOL axioms. We test if it is possible to prove an unprovable
-- theorem from these axioms.

module GroupTheory.Groupoids.Base.ConsistencyTest where

open import GroupTheory.Groupoids.Base

------------------------------------------------------------------------------

postulate
  impossible : (d e : G) → d ≡ e
{-# ATP prove impossible #-}
