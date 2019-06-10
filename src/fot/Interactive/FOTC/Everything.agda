------------------------------------------------------------------------------
-- All the FOTC modules
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOTC.Everything where

open import Interactive.FOTC.Base
open import Interactive.FOTC.Base.Consistency.IfInjective
open import Interactive.FOTC.Base.List
open import Interactive.FOTC.Base.List.Properties
open import Interactive.FOTC.Base.Loop
open import Interactive.FOTC.Base.Properties

open import Interactive.FOTC.Data.Bool
open import Interactive.FOTC.Data.Bool.Properties
open import Interactive.FOTC.Data.Bool.Type

open import Interactive.FOTC.Data.Colist
open import Interactive.FOTC.Data.Colist.Properties
open import Interactive.FOTC.Data.Colist.Type

open import Interactive.FOTC.Data.Conat
open import Interactive.FOTC.Data.Conat.Equality.Properties
open import Interactive.FOTC.Data.Conat.Equality.Type
open import Interactive.FOTC.Data.Conat.Properties
open import Interactive.FOTC.Data.Conat.Type

open import Interactive.FOTC.Data.List
open import Interactive.FOTC.Data.List.PropertiesByInduction
open import Interactive.FOTC.Data.List.Properties
open import Interactive.FOTC.Data.List.Type
open import Interactive.FOTC.Data.List.WF-Relation.LT-Cons
open import Interactive.FOTC.Data.List.WF-Relation.LT-Cons.Induction.Acc.WF
open import Interactive.FOTC.Data.List.WF-Relation.LT-Cons.Properties
open import Interactive.FOTC.Data.List.WF-Relation.LT-Length
open import Interactive.FOTC.Data.List.WF-Relation.LT-Length.Induction.Acc.WF
open import Interactive.FOTC.Data.List.WF-Relation.LT-Length.Properties

open import Interactive.FOTC.Data.Nat
open import Interactive.FOTC.Data.Nat.Divisibility.By0
open import Interactive.FOTC.Data.Nat.Divisibility.By0.Properties
open import Interactive.FOTC.Data.Nat.Divisibility.NotBy0
open import Interactive.FOTC.Data.Nat.Divisibility.NotBy0.Properties
open import Interactive.FOTC.Data.Nat.Divisibility.NotBy0.Properties
open import Interactive.FOTC.Data.Nat.Induction.Acc.WF
open import Interactive.FOTC.Data.Nat.Induction.NonAcc.Lexicographic
open import Interactive.FOTC.Data.Nat.Induction.NonAcc.WF
open import Interactive.FOTC.Data.Nat.Inequalities
open import Interactive.FOTC.Data.Nat.Inequalities.EliminationProperties
open import Interactive.FOTC.Data.Nat.Inequalities.Properties
open import Interactive.FOTC.Data.Nat.List
open import Interactive.FOTC.Data.Nat.List.Properties
open import Interactive.FOTC.Data.Nat.List.Type
open import Interactive.FOTC.Data.Nat.PropertiesByInduction
open import Interactive.FOTC.Data.Nat.Properties
open import Interactive.FOTC.Data.Nat.Type
open import Interactive.FOTC.Data.Nat.UnaryNumbers
open import Interactive.FOTC.Data.Nat.UnaryNumbers.Inequalities.Properties
open import Interactive.FOTC.Data.Nat.UnaryNumbers.Totality

open import Interactive.FOTC.Data.Stream
open import Interactive.FOTC.Data.Stream.Equality.Properties
open import Interactive.FOTC.Data.Stream.Properties
open import Interactive.FOTC.Data.Stream.Type

open import Interactive.FOTC.Induction.WF

open import Interactive.FOTC.Program.ABP.ABP
open import Interactive.FOTC.Program.ABP.CorrectnessProof
open import Interactive.FOTC.Program.ABP.Fair.Type
open import Interactive.FOTC.Program.ABP.Fair.Properties
open import Interactive.FOTC.Program.ABP.Lemma1
open import Interactive.FOTC.Program.ABP.Lemma2
open import Interactive.FOTC.Program.ABP.Properties
open import Interactive.FOTC.Program.ABP.Terms

open import Interactive.FOTC.Program.Collatz.Collatz
open import Interactive.FOTC.Program.Collatz.Data.Nat
open import Interactive.FOTC.Program.Collatz.Data.Nat.Properties
open import Interactive.FOTC.Program.Collatz.Properties

open import Interactive.FOTC.Program.Division.ConversionRules
open import Interactive.FOTC.Program.Division.CorrectnessProof
open import Interactive.FOTC.Program.Division.Division
open import Interactive.FOTC.Program.Division.Result
open import Interactive.FOTC.Program.Division.Specification
open import Interactive.FOTC.Program.Division.Totality

open import Interactive.FOTC.Program.GCD.Partial.CommonDivisor
open import Interactive.FOTC.Program.GCD.Partial.ConversionRules
open import Interactive.FOTC.Program.GCD.Partial.CorrectnessProof
open import Interactive.FOTC.Program.GCD.Partial.Definitions
open import Interactive.FOTC.Program.GCD.Partial.Divisible
open import Interactive.FOTC.Program.GCD.Partial.GCD
open import Interactive.FOTC.Program.GCD.Partial.GreatestAnyCommonDivisor
open import Interactive.FOTC.Program.GCD.Partial.Totality

open import Interactive.FOTC.Program.GCD.Total.CommonDivisor
open import Interactive.FOTC.Program.GCD.Total.ConversionRules
open import Interactive.FOTC.Program.GCD.Total.CorrectnessProof
open import Interactive.FOTC.Program.GCD.Total.Definitions
open import Interactive.FOTC.Program.GCD.Total.Divisible
open import Interactive.FOTC.Program.GCD.Total.GCD
open import Interactive.FOTC.Program.GCD.Total.Totality

open import Interactive.FOTC.Program.Iter0.Iter0
open import Interactive.FOTC.Program.Iter0.Properties

open import Interactive.FOTC.Program.MapIterate.MapIterate

open import Interactive.FOTC.Program.McCarthy91.Arithmetic
open import Interactive.FOTC.Program.McCarthy91.AuxiliaryProperties
open import Interactive.FOTC.Program.McCarthy91.McCarthy91
open import Interactive.FOTC.Program.McCarthy91.Properties
open import Interactive.FOTC.Program.McCarthy91.WF-Relation
open import Interactive.FOTC.Program.McCarthy91.WF-Relation.LT2WF-Relation
open import Interactive.FOTC.Program.McCarthy91.WF-Relation.Properties
open import Interactive.FOTC.Program.McCarthy91.WF-Relation.Induction.Acc.WF

open import Interactive.FOTC.Program.Mirror.Example
open import Interactive.FOTC.Program.Mirror.Forest.Properties
open import Interactive.FOTC.Program.Mirror.Forest.Totality
open import Interactive.FOTC.Program.Mirror.Mirror
open import Interactive.FOTC.Program.Mirror.Properties
open import Interactive.FOTC.Program.Mirror.Tree.Totality
open import Interactive.FOTC.Program.Mirror.Type

open import Interactive.FOTC.Program.Nest.Nest
open import Interactive.FOTC.Program.Nest.Properties

open import Interactive.FOTC.Program.SortList.CorrectnessProof
open import Interactive.FOTC.Program.SortList.Properties.Miscellaneous
open import Interactive.FOTC.Program.SortList.Properties.Totality.Bool
open import Interactive.FOTC.Program.SortList.Properties.Totality.ListN
open import Interactive.FOTC.Program.SortList.Properties.Totality.OrdList.Flatten
open import Interactive.FOTC.Program.SortList.Properties.Totality.OrdList
open import Interactive.FOTC.Program.SortList.Properties.Totality.OrdTree
open import Interactive.FOTC.Program.SortList.Properties.Totality.Tree
open import Interactive.FOTC.Program.SortList.Properties
open import Interactive.FOTC.Program.SortList.SortList

open import Interactive.FOTC.Relation.Binary.Bisimilarity.Bisimulation
open import Interactive.FOTC.Relation.Binary.Bisimilarity.Properties
open import Interactive.FOTC.Relation.Binary.Bisimilarity.Type
