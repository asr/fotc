------------------------------------------------------------------------------
-- All the FOTC modules
------------------------------------------------------------------------------

module FOTC.Everything where

open import FOTC.Base
open import FOTC.Base.Consistency.Axioms
open import FOTC.Base.Consistency.IfInjective
open import FOTC.Base.List
open import FOTC.Base.List.Consistency.Axioms
open import FOTC.Base.List.PropertiesATP
open import FOTC.Base.List.PropertiesI
open import FOTC.Base.Loop
open import FOTC.Base.PropertiesATP
open import FOTC.Base.PropertiesI

open import FOTC.Data.Bool
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Bool.PropertiesI
open import FOTC.Data.Bool.Type

open import FOTC.Data.Colist
open import FOTC.Data.Colist.Type
open import FOTC.Data.Colist.Type.Consistency.Axioms

open import FOTC.Data.Conat
open import FOTC.Data.Conat.Equality
open import FOTC.Data.Conat.Equality.Consistency.Axioms
open import FOTC.Data.Conat.Equality.PropertiesATP
open import FOTC.Data.Conat.Equality.PropertiesI
open import FOTC.Data.Conat.PropertiesATP
open import FOTC.Data.Conat.PropertiesI
open import FOTC.Data.Conat.Type
open import FOTC.Data.Conat.Type.Consistency.Axioms

open import FOTC.Data.List
open import FOTC.Data.List.Consistency.Axioms
open import FOTC.Data.List.PropertiesATP
open import FOTC.Data.List.PropertiesByInductionATP
open import FOTC.Data.List.PropertiesI
open import FOTC.Data.List.Type
open import FOTC.Data.List.WF-Relation.LT-Cons
open import FOTC.Data.List.WF-Relation.LT-Cons.Induction.Acc.WF-I
open import FOTC.Data.List.WF-Relation.LT-Cons.PropertiesI
open import FOTC.Data.List.WF-Relation.LT-Length
open import FOTC.Data.List.WF-Relation.LT-Length.Induction.Acc.WF-I
open import FOTC.Data.List.WF-Relation.LT-Length.PropertiesI

open import FOTC.Data.Nat
open import FOTC.Data.Nat.Consistency.Axioms
open import FOTC.Data.Nat.Divisibility.By0
open import FOTC.Data.Nat.Divisibility.By0.PropertiesATP
open import FOTC.Data.Nat.Divisibility.By0.PropertiesI
open import FOTC.Data.Nat.Divisibility.NotBy0
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI
open import FOTC.Data.Nat.Induction.Acc.WF-ATP
open import FOTC.Data.Nat.Induction.Acc.WF-I
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicATP
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI
open import FOTC.Data.Nat.Induction.NonAcc.WF-ATP
open import FOTC.Data.Nat.Induction.NonAcc.WF-I
open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.Consistency.Axioms
open import FOTC.Data.Nat.Inequalities.EliminationPropertiesATP
open import FOTC.Data.Nat.Inequalities.EliminationPropertiesI
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.Inequalities.PropertiesI
open import FOTC.Data.Nat.List
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
open import FOTC.Data.Stream.Equality.PropertiesATP
open import FOTC.Data.Stream.Equality.PropertiesI
open import FOTC.Data.Stream.PropertiesATP
open import FOTC.Data.Stream.PropertiesI
open import FOTC.Data.Stream.Type
open import FOTC.Data.Stream.Type.Consistency.Axioms

open import FOTC.Induction.WF

open import FOTC.Program.ABP.ABP
open import FOTC.Program.ABP.ABP.Consistency.Axioms
open import FOTC.Program.ABP.CorrectnessProofATP
open import FOTC.Program.ABP.CorrectnessProofI
open import FOTC.Program.ABP.DS.ABP
open import FOTC.Program.ABP.DS.CorrectnessProofATP
open import FOTC.Program.ABP.DS.CorrectnessProofI
open import FOTC.Program.ABP.DS.Lemma1ATP
open import FOTC.Program.ABP.DS.Lemma1I
open import FOTC.Program.ABP.DS.Lemma2ATP
open import FOTC.Program.ABP.DS.Lemma2I
open import FOTC.Program.ABP.Fair
open import FOTC.Program.ABP.Fair.Consistency.Axioms
open import FOTC.Program.ABP.Fair.PropertiesATP
open import FOTC.Program.ABP.Fair.PropertiesI
open import FOTC.Program.ABP.LemmaATP
open import FOTC.Program.ABP.LemmaI
open import FOTC.Program.ABP.PropertiesI
open import FOTC.Program.ABP.Terms

open import FOTC.Program.Collatz.Collatz
open import FOTC.Program.Collatz.Collatz.Consistency.Axioms
open import FOTC.Program.Collatz.Data.Nat
open import FOTC.Program.Collatz.Data.Nat.Consistency.Axioms
open import FOTC.Program.Collatz.Data.Nat.PropertiesATP
open import FOTC.Program.Collatz.Data.Nat.PropertiesI
open import FOTC.Program.Collatz.PropertiesI
open import FOTC.Program.Collatz.PropertiesATP

open import FOTC.Program.Division.ConversionRulesATP
open import FOTC.Program.Division.ConversionRulesI
open import FOTC.Program.Division.CorrectnessProofATP
open import FOTC.Program.Division.CorrectnessProofI
open import FOTC.Program.Division.Division
open import FOTC.Program.Division.ResultATP
open import FOTC.Program.Division.ResultI
open import FOTC.Program.Division.Specification
open import FOTC.Program.Division.TotalityATP
open import FOTC.Program.Division.TotalityI

open import FOTC.Program.GCD.Partial.CommonDivisorATP
open import FOTC.Program.GCD.Partial.CommonDivisorI
open import FOTC.Program.GCD.Partial.ConversionRulesATP
open import FOTC.Program.GCD.Partial.ConversionRulesI
open import FOTC.Program.GCD.Partial.CorrectnessProofATP
open import FOTC.Program.GCD.Partial.CorrectnessProofI
open import FOTC.Program.GCD.Partial.Definitions
open import FOTC.Program.GCD.Partial.DivisibleATP
open import FOTC.Program.GCD.Partial.DivisibleI
open import FOTC.Program.GCD.Partial.GCD
open import FOTC.Program.GCD.Partial.GCD.Consistency.Axioms
open import FOTC.Program.GCD.Partial.GreatestAnyCommonDivisor
open import FOTC.Program.GCD.Partial.TotalityATP
open import FOTC.Program.GCD.Partial.TotalityI

open import FOTC.Program.GCD.Total.CommonDivisorATP
open import FOTC.Program.GCD.Total.CommonDivisorI
open import FOTC.Program.GCD.Total.ConversionRulesATP
open import FOTC.Program.GCD.Total.ConversionRulesI
open import FOTC.Program.GCD.Total.CorrectnessProofATP
open import FOTC.Program.GCD.Total.CorrectnessProofI
open import FOTC.Program.GCD.Total.Definitions
open import FOTC.Program.GCD.Total.DivisibleATP
open import FOTC.Program.GCD.Total.DivisibleI
open import FOTC.Program.GCD.Total.GCD
open import FOTC.Program.GCD.Total.GCD.Consistency.Axioms
open import FOTC.Program.GCD.Total.TotalityATP
open import FOTC.Program.GCD.Total.TotalityI

open import FOTC.Program.Iter0.Iter0
open import FOTC.Program.Iter0.PropertiesATP
open import FOTC.Program.Iter0.PropertiesI

open import FOTC.Program.MapIterate.MapIterateATP
open import FOTC.Program.MapIterate.MapIterateI

open import FOTC.Program.McCarthy91.ArithmeticATP
open import FOTC.Program.McCarthy91.AuxiliaryPropertiesATP
open import FOTC.Program.McCarthy91.McCarthy91.Consistency.Axioms
open import FOTC.Program.McCarthy91.McCarthy91
open import FOTC.Program.McCarthy91.PropertiesATP
open import FOTC.Program.McCarthy91.WF-Relation
open import FOTC.Program.McCarthy91.WF-Relation.LT2WF-RelationATP
open import FOTC.Program.McCarthy91.WF-Relation.PropertiesATP
open import FOTC.Program.McCarthy91.WF-Relation.Induction.Acc.WF-ATP

open import FOTC.Program.Mirror.Forest.PropertiesATP
open import FOTC.Program.Mirror.Forest.PropertiesI
open import FOTC.Program.Mirror.Forest.TotalityATP
open import FOTC.Program.Mirror.Forest.TotalityI
open import FOTC.Program.Mirror.Mirror.Consistency.Axioms
open import FOTC.Program.Mirror.Mirror
open import FOTC.Program.Mirror.PropertiesATP
open import FOTC.Program.Mirror.PropertiesI
open import FOTC.Program.Mirror.Tree.TotalityATP
open import FOTC.Program.Mirror.Tree.TotalityI
open import FOTC.Program.Mirror.Type

open import FOTC.Program.Nest.Nest
open import FOTC.Program.Nest.Nest.Consistency.Axioms
open import FOTC.Program.Nest.PropertiesATP

open import FOTC.Program.SortList.CorrectnessProofATP
open import FOTC.Program.SortList.CorrectnessProofI
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
open import FOTC.Program.SortList.SortList.Consistency.Axioms

open import FOTC.Relation.Binary.Bisimilarity
open import FOTC.Relation.Binary.Bisimilarity.Consistency.Axioms
open import FOTC.Relation.Binary.Bisimilarity.PropertiesATP
open import FOTC.Relation.Binary.Bisimilarity.PropertiesI
