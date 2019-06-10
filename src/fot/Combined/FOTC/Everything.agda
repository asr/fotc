------------------------------------------------------------------------------
-- All the FOTC modules
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOTC.Everything where

open import Combined.FOTC.Base
open import Combined.FOTC.Base.Consistency.Axioms
open import Combined.FOTC.Base.Consistency.IfInjective
open import Combined.FOTC.Base.List
open import Combined.FOTC.Base.List.Consistency.Axioms
open import Combined.FOTC.Base.List.Properties
open import Combined.FOTC.Base.Loop
open import Combined.FOTC.Base.Properties

open import Combined.FOTC.Data.Bool
open import Combined.FOTC.Data.Bool.Properties
open import Combined.FOTC.Data.Bool.Type

open import Combined.FOTC.Data.Colist
open import Combined.FOTC.Data.Colist.Properties
open import Combined.FOTC.Data.Colist.Type
open import Combined.FOTC.Data.Colist.Type.Consistency.Axioms

open import Combined.FOTC.Data.Conat
open import Combined.FOTC.Data.Conat.Equality.Consistency.Axioms
open import Combined.FOTC.Data.Conat.Equality.Properties
open import Combined.FOTC.Data.Conat.Equality.Type
open import Combined.FOTC.Data.Conat.Properties
open import Combined.FOTC.Data.Conat.Type
open import Combined.FOTC.Data.Conat.Type.Consistency.Axioms

open import Combined.FOTC.Data.List
open import Combined.FOTC.Data.List.Consistency.Axioms
open import Combined.FOTC.Data.List.Properties
open import Combined.FOTC.Data.List.Properties
open import Combined.FOTC.Data.List.PropertiesByInduction
open import Combined.FOTC.Data.List.Type
open import Combined.FOTC.Data.List.WF-Relation.LT-Cons
open import Combined.FOTC.Data.List.WF-Relation.LT-Cons.Induction.Acc.WF
open import Combined.FOTC.Data.List.WF-Relation.LT-Cons.Properties
open import Combined.FOTC.Data.List.WF-Relation.LT-Length
open import Combined.FOTC.Data.List.WF-Relation.LT-Length.Induction.Acc.WF
open import Combined.FOTC.Data.List.WF-Relation.LT-Length.Properties

open import Combined.FOTC.Data.Nat
open import Combined.FOTC.Data.Nat.Consistency.Axioms
open import Combined.FOTC.Data.Nat.Divisibility.By0
open import Combined.FOTC.Data.Nat.Divisibility.By0.Properties
open import Combined.FOTC.Data.Nat.Divisibility.NotBy0
open import Combined.FOTC.Data.Nat.Divisibility.NotBy0.Properties
open import Combined.FOTC.Data.Nat.Induction.Acc.WF
open import Combined.FOTC.Data.Nat.Induction.NonAcc.Lexicographic
open import Combined.FOTC.Data.Nat.Induction.NonAcc.WF
open import Combined.FOTC.Data.Nat.Inequalities
open import Combined.FOTC.Data.Nat.Inequalities.Consistency.Axioms
open import Combined.FOTC.Data.Nat.Inequalities.EliminationProperties
open import Combined.FOTC.Data.Nat.Inequalities.Properties
open import Combined.FOTC.Data.Nat.List
open import Combined.FOTC.Data.Nat.List.Properties
open import Combined.FOTC.Data.Nat.List.Type
open import Combined.FOTC.Data.Nat.Properties
open import Combined.FOTC.Data.Nat.PropertiesByInduction
open import Combined.FOTC.Data.Nat.Type
open import Combined.FOTC.Data.Nat.UnaryNumbers
open import Combined.FOTC.Data.Nat.UnaryNumbers.Inequalities.Properties
open import Combined.FOTC.Data.Nat.UnaryNumbers.Totality

open import Combined.FOTC.Data.Stream
open import Combined.FOTC.Data.Stream.Equality.Properties
open import Combined.FOTC.Data.Stream.Properties
open import Combined.FOTC.Data.Stream.Type
open import Combined.FOTC.Data.Stream.Type.Consistency.Axioms

open import Combined.FOTC.Induction.WF

open import Combined.FOTC.Program.ABP.ABP
open import Combined.FOTC.Program.ABP.ABP.Consistency.Axioms
open import Combined.FOTC.Program.ABP.CorrectnessProof
open import Combined.FOTC.Program.ABP.Fair.Type
open import Combined.FOTC.Program.ABP.Fair.Consistency.Axioms
open import Combined.FOTC.Program.ABP.Fair.Properties
open import Combined.FOTC.Program.ABP.Lemma1
open import Combined.FOTC.Program.ABP.Lemma2
open import Combined.FOTC.Program.ABP.Terms

open import Combined.FOTC.Program.Collatz.Collatz
open import Combined.FOTC.Program.Collatz.Collatz.Consistency.Axioms
open import Combined.FOTC.Program.Collatz.Data.Nat
open import Combined.FOTC.Program.Collatz.Data.Nat.Consistency.Axioms
open import Combined.FOTC.Program.Collatz.Data.Nat.Properties
open import Combined.FOTC.Program.Collatz.Properties

open import Combined.FOTC.Program.Division.ConversionRules
open import Combined.FOTC.Program.Division.CorrectnessProof
open import Combined.FOTC.Program.Division.Division
open import Combined.FOTC.Program.Division.Result
open import Combined.FOTC.Program.Division.Specification
open import Combined.FOTC.Program.Division.Totality

open import Combined.FOTC.Program.GCD.Partial.CommonDivisor
open import Combined.FOTC.Program.GCD.Partial.ConversionRules
open import Combined.FOTC.Program.GCD.Partial.CorrectnessProof
open import Combined.FOTC.Program.GCD.Partial.Definitions
open import Combined.FOTC.Program.GCD.Partial.Divisible
open import Combined.FOTC.Program.GCD.Partial.GCD
open import Combined.FOTC.Program.GCD.Partial.GCD.Consistency.Axioms
open import Combined.FOTC.Program.GCD.Partial.GreatestAnyCommonDivisor
open import Combined.FOTC.Program.GCD.Partial.Totality

open import Combined.FOTC.Program.GCD.Total.CommonDivisor
open import Combined.FOTC.Program.GCD.Total.ConversionRules
open import Combined.FOTC.Program.GCD.Total.CorrectnessProof
open import Combined.FOTC.Program.GCD.Total.Definitions
open import Combined.FOTC.Program.GCD.Total.Divisible
open import Combined.FOTC.Program.GCD.Total.Divisible
open import Combined.FOTC.Program.GCD.Total.GCD
open import Combined.FOTC.Program.GCD.Total.GCD.Consistency.Axioms
open import Combined.FOTC.Program.GCD.Total.Totality

open import Combined.FOTC.Program.Iter0.Iter0
open import Combined.FOTC.Program.Iter0.Properties

open import Combined.FOTC.Program.MapIterate.MapIterate

open import Combined.FOTC.Program.McCarthy91.Arithmetic
open import Combined.FOTC.Program.McCarthy91.AuxiliaryProperties
open import Combined.FOTC.Program.McCarthy91.McCarthy91.Consistency.Axioms
open import Combined.FOTC.Program.McCarthy91.McCarthy91
open import Combined.FOTC.Program.McCarthy91.Properties
open import Combined.FOTC.Program.McCarthy91.WF-Relation
open import Combined.FOTC.Program.McCarthy91.WF-Relation.Induction.Acc.WF
open import Combined.FOTC.Program.McCarthy91.WF-Relation.LT2WF-Relation
open import Combined.FOTC.Program.McCarthy91.WF-Relation.Properties

open import Combined.FOTC.Program.Mirror.Example
open import Combined.FOTC.Program.Mirror.Forest.Properties
open import Combined.FOTC.Program.Mirror.Forest.Totality
open import Combined.FOTC.Program.Mirror.Mirror.Consistency.Axioms
open import Combined.FOTC.Program.Mirror.Mirror
open import Combined.FOTC.Program.Mirror.Properties
open import Combined.FOTC.Program.Mirror.Tree.Totality
open import Combined.FOTC.Program.Mirror.Type

open import Combined.FOTC.Program.Nest.Nest
open import Combined.FOTC.Program.Nest.Nest.Consistency.Axioms
open import Combined.FOTC.Program.Nest.Properties

open import Combined.FOTC.Program.SortList.CorrectnessProof
open import Combined.FOTC.Program.SortList.Properties.Miscellaneous
open import Combined.FOTC.Program.SortList.Properties.Totality.Bool
open import Combined.FOTC.Program.SortList.Properties.Totality.ListN
open import Combined.FOTC.Program.SortList.Properties.Totality.OrdList.Flatten
open import Combined.FOTC.Program.SortList.Properties.Totality.OrdList
open import Combined.FOTC.Program.SortList.Properties.Totality.OrdTree
open import Combined.FOTC.Program.SortList.Properties.Totality.Tree
open import Combined.FOTC.Program.SortList.Properties
open import Combined.FOTC.Program.SortList.SortList
open import Combined.FOTC.Program.SortList.SortList.Consistency.Axioms

open import Combined.FOTC.Relation.Binary.Bisimilarity.Bisimulation
open import Combined.FOTC.Relation.Binary.Bisimilarity.Consistency.Axioms
open import Combined.FOTC.Relation.Binary.Bisimilarity.Properties
open import Combined.FOTC.Relation.Binary.Bisimilarity.Type
