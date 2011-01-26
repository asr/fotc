------------------------------------------------------------------------------
-- Test the consistency of LTC.Program.SortList.SortList
------------------------------------------------------------------------------

-- In the module LTC.Program.SortList.SortList we declare Agda
-- postulates as FOL axioms. We test if it is possible to prove an
-- unprovable theorem from these axioms.

module LTC.Program.SortList.SortList.ConsistencyTest where

open import LTC.Base

open import LTC.Program.SortList.SortList

------------------------------------------------------------------------------

postulate
  impossible : ∀ d e → d ≡ e
{-# ATP prove impossible #-}
