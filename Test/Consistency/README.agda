------------------------------------------------------------------------------
-- Test the consistency of the axioms
------------------------------------------------------------------------------
-- In some modules, we declare Agda postulates as FOL axioms. We
-- test in these modules if it is possible to prove an unprovable
-- theorem from these axioms (see the rule all_consistency in
-- src/Makefile).

module Test.Consistency.README where

open import Test.Consistency.LTC.Base.Impossible
open import Test.Consistency.LTC.Data.Bool.Impossible
open import Test.Consistency.LTC.Data.List.Impossible
open import Test.Consistency.LTC.Data.Nat.Impossible
open import Test.Consistency.LTC.Data.Nat.Inequalities.Impossible
open import Test.Consistency.LTC.Data.Stream.Bisimilarity.Impossible
open import Test.Consistency.LTC.Program.GCD.GCD.Impossible
open import Test.Consistency.LTC.Program.SortList.SortList.Impossible

open import Test.Consistency.GroupTheory.Base.Impossible

