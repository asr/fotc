------------------------------------------------------------------------------
-- All the FOTC modules
------------------------------------------------------------------------------

module FOTC.Everything where

open import FOTC.Base
open import FOTC.Base.ConsistencyTest
open import FOTC.Base.Properties
open import FOTC.Base.PropertiesATP
open import FOTC.Base.PropertiesI

open import FOTC.Data.Bool
open import FOTC.Data.Bool.ConsistencyTest
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Bool.Type

open import FOTC.Data.List
open import FOTC.Data.List.ConsistencyTest
open import FOTC.Data.List.Induction.Acc.WellFounded
open import FOTC.Data.List.Length.PropertiesATP
open import FOTC.Data.List.Length.PropertiesI
open import FOTC.Data.List.LT-Cons
open import FOTC.Data.List.LT-Cons.Induction.Acc.WellFoundedInduction
open import FOTC.Data.List.LT-Cons.PropertiesI
open import FOTC.Data.List.LT-Length
open import FOTC.Data.List.LT-Length.Induction.Acc.WellFoundedInduction
open import FOTC.Data.List.LT-Length.PropertiesI
open import FOTC.Data.List.PropertiesATP
open import FOTC.Data.List.PropertiesByInductionATP
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.List.Type

open import FOTC.Data.Nat
open import FOTC.Data.Nat.ConsistencyTest
open import FOTC.Data.Nat.Divisibility
open import FOTC.Data.Nat.Divisibility.Properties
open import FOTC.Data.Nat.Divisibility.PropertiesATP
open import FOTC.Data.Nat.Divisibility.PropertiesI
open import FOTC.Data.Nat.Induction.Acc.WellFounded
open import FOTC.Data.Nat.Induction.Acc.WellFoundedInduction
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicATP
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Induction.NonAcc.WellFoundedInduction
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.ConsistencyTest
open import FOTC.Data.Nat.Inequalities.Properties
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.List.PropertiesATP
open import FOTC.Data.Nat.List.PropertiesI
open import FOTC.Data.Nat.List.Type
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.PropertiesByInductionATP
open import FOTC.Data.Nat.PropertiesByInductionI
open import FOTC.Data.Nat.PropertiesI
open import FOTC.Data.Nat.Type
open import FOTC.Data.Nat.UnaryNumbers
open import FOTC.Data.Nat.UnaryNumbers.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers.IsN-ATP

open import FOTC.Data.Stream.Bisimilarity
open import FOTC.Data.Stream.Bisimilarity.ConsistencyTest
open import FOTC.Data.Stream.Bisimilarity.PropertiesATP
open import FOTC.Data.Stream.Bisimilarity.PropertiesI

open import FOTC.Program.GCD.Definitions
open import FOTC.Program.GCD.GCD
open import FOTC.Program.GCD.GCD.ConsistencyTest
open import FOTC.Program.GCD.IsCommonDivisorATP
open import FOTC.Program.GCD.IsCommonDivisorI
open import FOTC.Program.GCD.IsDivisibleATP
open import FOTC.Program.GCD.IsDivisibleI
open import FOTC.Program.GCD.IsGreatestAnyCommonDivisor
open import FOTC.Program.GCD.IsN-ATP
open import FOTC.Program.GCD.IsN-I
open import FOTC.Program.GCD.ProofSpecificationATP
open import FOTC.Program.GCD.ProofSpecificationI
open import FOTC.Program.GCD.Specification

open import FOTC.Program.McCarthy91.ArithmeticATP
open import FOTC.Program.McCarthy91.McCarthy91.ConsistencyTest
open import FOTC.Program.McCarthy91.McCarthy91
open import FOTC.Program.McCarthy91.MCR
open import FOTC.Program.McCarthy91.MCR.LT2MCR-ATP
open import FOTC.Program.McCarthy91.MCR.PropertiesATP
open import FOTC.Program.McCarthy91.MCR.Induction.Acc.WellFoundedInductionATP
open import FOTC.Program.McCarthy91.Properties.AuxiliaryATP
open import FOTC.Program.McCarthy91.Properties.MainATP

open import FOTC.Program.Mirror.ListTree.Closures
open import FOTC.Program.Mirror.ListTree.PropertiesATP
open import FOTC.Program.Mirror.ListTree.PropertiesI
open import FOTC.Program.Mirror.Mirror.ConsistencyTest
open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.PropertiesATP
open import FOTC.Program.Mirror.PropertiesI
open import FOTC.Program.Mirror.Tree.ClosuresATP
open import FOTC.Program.Mirror.Tree.ClosuresI
open import FOTC.Program.Mirror.Type

open import FOTC.Program.SortList.ProofSpecificationATP
open import FOTC.Program.SortList.ProofSpecificationI
open import FOTC.Program.SortList.Properties.Closures.BoolATP
open import FOTC.Program.SortList.Properties.Closures.BoolI
open import FOTC.Program.SortList.Properties.Closures.ListN-ATP
open import FOTC.Program.SortList.Properties.Closures.ListN-I
open import FOTC.Program.SortList.Properties.Closures.OrdList.FlattenI
open import FOTC.Program.SortList.Properties.Closures.OrdList.FlattenATP
open import FOTC.Program.SortList.Properties.Closures.OrdListATP
open import FOTC.Program.SortList.Properties.Closures.OrdListI
open import FOTC.Program.SortList.Properties.Closures.OrdTreeATP
open import FOTC.Program.SortList.Properties.Closures.OrdTreeI
open import FOTC.Program.SortList.Properties.Closures.TreeATP
open import FOTC.Program.SortList.Properties.Closures.TreeI
open import FOTC.Program.SortList.Properties.MiscellaneousATP
open import FOTC.Program.SortList.Properties.MiscellaneousI
open import FOTC.Program.SortList.PropertiesI
open import FOTC.Program.SortList.PropertiesATP
open import FOTC.Program.SortList.SortList
open import FOTC.Program.SortList.SortList.ConsistencyTest

open import FOTC.Relation.Binary.EqReasoning
