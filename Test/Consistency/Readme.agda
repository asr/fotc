------------------------------------------------------------------------------
-- Test the consistency of the LTC axioms
------------------------------------------------------------------------------

-- In some modules, we declare Agda postulates as FOL axioms. We
-- test in these modules if it is possible to prove an unprovable
-- theorem from these axioms.

module Test.Consistency.Readme where

open import Test.Consistency.LTC.Base
open import Test.Consistency.LTC.Data.Bool
open import Test.Consistency.LTC.Data.List
open import Test.Consistency.LTC.Data.Nat
open import Test.Consistency.LTC.Data.Nat.Inequalities
open import Test.Consistency.LTC.Data.Stream.Bisimilarity
