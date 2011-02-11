------------------------------------------------------------------------------
-- All the LTC modules
------------------------------------------------------------------------------

module LTC.Everything where

open import LTC.Base
open import LTC.Base.ConsistencyTest
open import LTC.Base.Properties
open import LTC.Base.PropertiesATP
open import LTC.Base.PropertiesI

open import LTC.Data.Bool
open import LTC.Data.Bool.ConsistencyTest
open import LTC.Data.Bool.PropertiesATP
open import LTC.Data.Bool.PropertiesI
open import LTC.Data.Bool.Type

open import LTC.Data.List
open import LTC.Data.List.ConsistencyTest
open import LTC.Data.List.PropertiesATP
open import LTC.Data.List.PropertiesByInductionATP
open import LTC.Data.List.PropertiesI
open import LTC.Data.List.Type

open import LTC.Data.Nat
open import LTC.Data.Nat.ConsistencyTest
open import LTC.Data.Nat.Divisibility
open import LTC.Data.Nat.Divisibility.Properties
open import LTC.Data.Nat.Divisibility.PropertiesATP
open import LTC.Data.Nat.Divisibility.PropertiesI
open import LTC.Data.Nat.Induction.LexicographicATP
open import LTC.Data.Nat.Induction.LexicographicI
open import LTC.Data.Nat.Induction.WellFoundedI
open import LTC.Data.Nat.Induction.WellFoundedATP
open import LTC.Data.Nat.Inequalities
open import LTC.Data.Nat.Inequalities.ConsistencyTest
open import LTC.Data.Nat.Inequalities.Properties
open import LTC.Data.Nat.Inequalities.PropertiesATP
open import LTC.Data.Nat.Inequalities.PropertiesI
open import LTC.Data.Nat.List.PropertiesATP
open import LTC.Data.Nat.List.PropertiesI
open import LTC.Data.Nat.List.Type
open import LTC.Data.Nat.PropertiesATP
open import LTC.Data.Nat.PropertiesByInductionATP
open import LTC.Data.Nat.PropertiesByInductionI
open import LTC.Data.Nat.PropertiesI
open import LTC.Data.Nat.Type
open import LTC.Data.Nat.Unary.Numbers

open import LTC.Data.Stream.Bisimilarity
open import LTC.Data.Stream.Bisimilarity.ConsistencyTest
open import LTC.Data.Stream.Bisimilarity.PropertiesATP
open import LTC.Data.Stream.Bisimilarity.PropertiesI

open import LTC.Program.GCD.Definitions
open import LTC.Program.GCD.GCD
open import LTC.Program.GCD.GCD.ConsistencyTest
open import LTC.Program.GCD.IsCommonDivisorATP
open import LTC.Program.GCD.IsCommonDivisorI
open import LTC.Program.GCD.IsDivisibleATP
open import LTC.Program.GCD.IsDivisibleI
open import LTC.Program.GCD.IsGreatestAnyCommonDivisor
open import LTC.Program.GCD.IsN-ATP
open import LTC.Program.GCD.IsN-I
open import LTC.Program.GCD.ProofSpecificationATP
open import LTC.Program.GCD.ProofSpecificationI
open import LTC.Program.GCD.Specification

open import LTC.Program.SortList.ProofSpecificationATP
open import LTC.Program.SortList.ProofSpecificationI
open import LTC.Program.SortList.Properties.Closures.BoolATP
open import LTC.Program.SortList.Properties.Closures.BoolI
open import LTC.Program.SortList.Properties.Closures.ListN-ATP
open import LTC.Program.SortList.Properties.Closures.ListN-I
open import LTC.Program.SortList.Properties.Closures.OrdList.FlattenI
open import LTC.Program.SortList.Properties.Closures.OrdList.FlattenATP
open import LTC.Program.SortList.Properties.Closures.OrdListATP
open import LTC.Program.SortList.Properties.Closures.OrdListI
open import LTC.Program.SortList.Properties.Closures.OrdTreeATP
open import LTC.Program.SortList.Properties.Closures.OrdTreeI
open import LTC.Program.SortList.Properties.Closures.TreeATP
open import LTC.Program.SortList.Properties.Closures.TreeI
open import LTC.Program.SortList.Properties.MiscellaneousATP
open import LTC.Program.SortList.Properties.MiscellaneousI
open import LTC.Program.SortList.PropertiesI
open import LTC.Program.SortList.PropertiesATP
open import LTC.Program.SortList.SortList
open import LTC.Program.SortList.SortList.ConsistencyTest

open import LTC.Relation.Binary.EqReasoning
