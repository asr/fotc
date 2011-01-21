------------------------------------------------------------------------------
-- Test the consistency of PA.Axiomatic.Base
------------------------------------------------------------------------------

-- In the module PA.Axiomatic.Base we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module PA.Axiomatic.Base.ConsistencyTest where

open import PA.Axiomatic.Base

------------------------------------------------------------------------------

postulate
  impossible : (m n : ℕ) → m ≣ n
{-# ATP prove impossible #-}
