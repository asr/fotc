------------------------------------------------------------------------------
-- Test the consistency of GroupTheory.Base
------------------------------------------------------------------------------

-- In the module GroupTheory.Base we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module GroupTheory.Base.ConsistencyTest where

open import GroupTheory.Base

------------------------------------------------------------------------------

postulate impossible : (d e : G) → d ≡ e
{-# ATP prove impossible #-}
