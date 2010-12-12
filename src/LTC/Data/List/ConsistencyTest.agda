------------------------------------------------------------------------------
-- Test the consistency of LTC.Data.List
------------------------------------------------------------------------------

-- In the module LTC.Data.List we declare Agda postulates as FOL
-- axioms. We test if it is possible to prove an unprovable theorem
-- from these axioms.

module LTC.Data.List.ConsistencyTest where

open import LTC.Base

open import LTC.Data.List

------------------------------------------------------------------------------

postulate
  impossible : (d e : D) → d ≡ e
{-# ATP prove impossible #-}
