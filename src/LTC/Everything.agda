------------------------------------------------------------------------------
-- All the LTC modules
------------------------------------------------------------------------------

module LTC.Everything where

open import LTC.Base
open import LTC.Base.Properties

open import LTC.Data.Bool
open import LTC.Data.Bool.Properties
open import LTC.Data.Bool.Type

open import LTC.Data.List
open import LTC.Data.List.Properties
open import LTC.Data.List.PropertiesByInduction
open import LTC.Data.List.Type

open import LTC.Data.Nat
open import LTC.Data.Nat.Divisibility
open import LTC.Data.Nat.Divisibility.Properties
open import LTC.Data.Nat.Induction.Lexicographic
open import LTC.Data.Nat.Induction.WellFounded
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.Properties
open import LTC.Data.Nat.List.Properties
open import LTC.Data.Nat.List.Type
open import LTC.Data.Nat.Properties
open import LTC.Data.Nat.PropertiesByInduction
open import LTC.Data.Nat.Type

open import LTC.Data.Stream.Bisimilarity
open import LTC.Data.Stream.Bisimilarity.Properties

open import LTC.Postulates

open import LTC.Program.GCD.GCD
open import LTC.Program.GCD.IsCommonDivisor
open import LTC.Program.GCD.IsDivisible
open import LTC.Program.GCD.IsGreatestAnyCommonDivisor
open import LTC.Program.GCD.IsN
open import LTC.Program.GCD.ProofSpecification

open import LTC.Program.SortList.Closures.Bool
open import LTC.Program.SortList.Closures.List
open import LTC.Program.SortList.Closures.ListOrd
open import LTC.Program.SortList.Closures.Tree
open import LTC.Program.SortList.Closures.TreeOrd
open import LTC.Program.SortList.ProofSpecification
open import LTC.Program.SortList.Properties
open import LTC.Program.SortList.SortList
