------------------------------------------------------------------------------
-- Test the consistency of AxiomaticPA.Base
------------------------------------------------------------------------------

-- In the module AxiomaticPA.Base we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module AxiomaticPA.Base.ConsistencyTest where

open import AxiomaticPA.Base

------------------------------------------------------------------------------

postulate
  impossible : (m n : ℕ) → m ≡ n
{-# ATP prove impossible #-}
