------------------------------------------------------------------------------
-- Test the consistency of GroupTheory.AbelianGroup.Base
------------------------------------------------------------------------------

-- In the module GroupTheory.AbelianGroup.Base we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module GroupTheory.AbelianGroup.Base.ConsistencyTest where

open import GroupTheory.AbelianGroup.Base

------------------------------------------------------------------------------

postulate impossible : (d e : G) → d ≡ e
{-# ATP prove impossible #-}
