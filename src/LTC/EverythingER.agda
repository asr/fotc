------------------------------------------------------------------------------
-- All the LTC properties and programs using equational reasoning
------------------------------------------------------------------------------

module LTC.EverythingER where

open import LTC.Base.PropertiesER

open import LTC.Data.Bool.PropertiesER
open import LTC.Data.List.PropertiesER
open import LTC.Data.Nat.Divisibility.PropertiesER
open import LTC.Data.Nat.Inequalities.PropertiesER
open import LTC.Data.Nat.List.PropertiesER
open import LTC.Data.Nat.PropertiesER
open import LTC.Data.Stream.Bisimilarity.PropertiesER

open import LTC.Program.GCD.IsCommonDivisorER
open import LTC.Program.GCD.IsDivisibleER
open import LTC.Program.GCD.IsGreatestAnyCommonDivisorER
open import LTC.Program.GCD.IsN-ER
open import LTC.Program.GCD.ProofSpecificationER

open import LTC.Program.SortList.Closures.BoolER
open import LTC.Program.SortList.Closures.ListER
open import LTC.Program.SortList.Closures.ListOrdER
open import LTC.Program.SortList.Closures.TreeER
open import LTC.Program.SortList.Closures.TreeOrdER
open import LTC.Program.SortList.ProofSpecificationER
open import LTC.Program.SortList.PropertiesER
