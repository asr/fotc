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

open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.Conat.Equality.ConsistencyTest
open import FOTC.Data.Conat.PropertiesI
open import FOTC.Data.Conat.Type
open import FOTC.Data.Conat.Type.ConsistencyTest

open import FOTC.Data.List
open import FOTC.Data.List.ConsistencyTest
open import FOTC.Data.List.LT-Cons
open import FOTC.Data.List.LT-Cons.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.List.LT-Cons.PropertiesI
open import FOTC.Data.List.LT-Length
open import FOTC.Data.List.LT-Length.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.List.LT-Length.PropertiesI
open import FOTC.Data.List.PropertiesATP
open import FOTC.Data.List.PropertiesByInductionATP
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.List.Type

open import FOTC.Data.Nat
open import FOTC.Data.Nat.ConsistencyTest
open import FOTC.Data.Nat.Divisibility.By0
open import FOTC.Data.Nat.Divisibility.By0.Properties
open import FOTC.Data.Nat.Divisibility.By0.PropertiesATP
open import FOTC.Data.Nat.Divisibility.By0.PropertiesI
open import FOTC.Data.Nat.Divisibility.NotBy0
open import FOTC.Data.Nat.Divisibility.NotBy0.Properties
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI
open import FOTC.Data.Nat.Induction.Acc.WellFoundedInductionATP
open import FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicATP
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Induction.NonAcc.WellFoundedInductionATP
open import FOTC.Data.Nat.Induction.NonAcc.WellFoundedInductionI
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.ConsistencyTest
open import FOTC.Data.Nat.Inequalities.EliminationProperties
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
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP
open import FOTC.Data.Nat.UnaryNumbers.TotalityI

open import FOTC.Data.Stream
open import FOTC.Data.Stream.Equality
open import FOTC.Data.Stream.Equality.ConsistencyTest
open import FOTC.Data.Stream.Equality.PropertiesATP
open import FOTC.Data.Stream.Equality.PropertiesI
open import FOTC.Data.Stream.PropertiesATP
open import FOTC.Data.Stream.PropertiesI
open import FOTC.Data.Stream.Type
open import FOTC.Data.Stream.Type.ConsistencyTest

open import FOTC.Induction.WellFounded

open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.ABP.ConsistencyTest
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.ConsistencyTest
open import FOTC.Program.ABP.Fair.PropertiesATP
open import FOTC.Program.ABP.Fair.PropertiesI
open import FOTC.Program.ABP.Lemma1.HelperATP
open import FOTC.Program.ABP.Lemma1.HelperI
open import FOTC.Program.ABP.Lemma1ATP
open import FOTC.Program.ABP.Lemma1I
open import FOTC.Program.ABP.Lemma2.HelperATP
open import FOTC.Program.ABP.Lemma2.HelperI
open import FOTC.Program.ABP.Lemma2ATP
open import FOTC.Program.ABP.Lemma2I
open import FOTC.Program.ABP.MayorPremiseATP
open import FOTC.Program.ABP.MayorPremiseI
open import FOTC.Program.ABP.MinorPremiseATP
open import FOTC.Program.ABP.MinorPremiseI
open import FOTC.Program.ABP.ProofSpecificationATP
open import FOTC.Program.ABP.ProofSpecificationI
open import FOTC.Program.ABP.Terms

open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Collatz.ConsistencyTest
open import FOTC.Program.Collatz.Data.Nat
open import FOTC.Program.Collatz.Data.Nat.ConsistencyTest
open import FOTC.Program.Collatz.Data.Nat.PropertiesATP
open import FOTC.Program.Collatz.Data.Nat.PropertiesI
open import FOTC.Program.Collatz.EquationsATP
open import FOTC.Program.Collatz.EquationsI
open import FOTC.Program.Collatz.PropertiesI
open import FOTC.Program.Collatz.PropertiesATP

open import FOTC.Program.Division.Division
open import FOTC.Program.Division.EquationsATP
open import FOTC.Program.Division.EquationsI
open import FOTC.Program.Division.IsCorrectATP
open import FOTC.Program.Division.IsCorrectI
open import FOTC.Program.Division.ProofSpecificationATP
open import FOTC.Program.Division.ProofSpecificationI
open import FOTC.Program.Division.Specification
open import FOTC.Program.Division.TotalityATP
open import FOTC.Program.Division.TotalityI

open import FOTC.Program.GCD.Partial.CommonDivisorATP
open import FOTC.Program.GCD.Partial.CommonDivisorI
open import FOTC.Program.GCD.Partial.Definitions
open import FOTC.Program.GCD.Partial.DivisibleATP
open import FOTC.Program.GCD.Partial.DivisibleI
open import FOTC.Program.GCD.Partial.EquationsATP
open import FOTC.Program.GCD.Partial.EquationsI
open import FOTC.Program.GCD.Partial.GCD
open import FOTC.Program.GCD.Partial.GCD.ConsistencyTest
open import FOTC.Program.GCD.Partial.GreatestAnyCommonDivisor
open import FOTC.Program.GCD.Partial.ProofSpecificationATP
open import FOTC.Program.GCD.Partial.ProofSpecificationI
open import FOTC.Program.GCD.Partial.Specification
open import FOTC.Program.GCD.Partial.TotalityATP
open import FOTC.Program.GCD.Partial.TotalityI

open import FOTC.Program.GCD.Total.CommonDivisorATP
open import FOTC.Program.GCD.Total.CommonDivisorI
open import FOTC.Program.GCD.Total.Definitions
open import FOTC.Program.GCD.Total.DivisibleATP
open import FOTC.Program.GCD.Total.DivisibleI
open import FOTC.Program.GCD.Total.EquationsATP
open import FOTC.Program.GCD.Total.EquationsI
open import FOTC.Program.GCD.Total.GCD
open import FOTC.Program.GCD.Total.GCD.ConsistencyTest
open import FOTC.Program.GCD.Total.ProofSpecificationATP
open import FOTC.Program.GCD.Total.ProofSpecificationI
open import FOTC.Program.GCD.Total.Specification
open import FOTC.Program.GCD.Total.TotalityATP
open import FOTC.Program.GCD.Total.TotalityI

open import FOTC.Program.MapIterate.MapIterateATP

open import FOTC.Program.McCarthy91.ArithmeticATP
open import FOTC.Program.McCarthy91.McCarthy91.ConsistencyTest
open import FOTC.Program.McCarthy91.McCarthy91
open import FOTC.Program.McCarthy91.MCR
open import FOTC.Program.McCarthy91.MCR.LT2MCR-ATP
open import FOTC.Program.McCarthy91.MCR.PropertiesATP
open import FOTC.Program.McCarthy91.MCR.Induction.Acc.WellFoundedInductionATP
open import FOTC.Program.McCarthy91.Properties.AuxiliaryATP
open import FOTC.Program.McCarthy91.Properties.MainATP

open import FOTC.Program.Mirror.Forest.PropertiesATP
open import FOTC.Program.Mirror.Forest.PropertiesI
open import FOTC.Program.Mirror.Forest.Totality
open import FOTC.Program.Mirror.Mirror.ConsistencyTest
open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.PropertiesATP
open import FOTC.Program.Mirror.PropertiesI
open import FOTC.Program.Mirror.Tree.Totality
open import FOTC.Program.Mirror.Type

open import FOTC.Program.SortList.ProofSpecificationATP
open import FOTC.Program.SortList.ProofSpecificationI
open import FOTC.Program.SortList.Properties.MiscellaneousATP
open import FOTC.Program.SortList.Properties.MiscellaneousI
open import FOTC.Program.SortList.Properties.Totality.BoolATP
open import FOTC.Program.SortList.Properties.Totality.BoolI
open import FOTC.Program.SortList.Properties.Totality.ListN-ATP
open import FOTC.Program.SortList.Properties.Totality.ListN-I
open import FOTC.Program.SortList.Properties.Totality.OrdList.FlattenI
open import FOTC.Program.SortList.Properties.Totality.OrdList.FlattenATP
open import FOTC.Program.SortList.Properties.Totality.OrdListATP
open import FOTC.Program.SortList.Properties.Totality.OrdListI
open import FOTC.Program.SortList.Properties.Totality.OrdTreeATP
open import FOTC.Program.SortList.Properties.Totality.OrdTreeI
open import FOTC.Program.SortList.Properties.Totality.TreeATP
open import FOTC.Program.SortList.Properties.Totality.TreeI
open import FOTC.Program.SortList.PropertiesI
open import FOTC.Program.SortList.PropertiesATP
open import FOTC.Program.SortList.SortList
open import FOTC.Program.SortList.SortList.ConsistencyTest

open import FOTC.Relation.Binary.EqReasoning
