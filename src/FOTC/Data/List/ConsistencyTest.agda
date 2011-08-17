------------------------------------------------------------------------------
-- Test the consistency of FOTC.Data.List
------------------------------------------------------------------------------

-- In the module FOTC.Data.List we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module FOTC.Data.List.ConsistencyTest where

open import FOTC.Base

open import FOTC.Data.List

------------------------------------------------------------------------------

postulate impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
