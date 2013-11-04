------------------------------------------------------------------------------
-- First-Order Theory of Combinators (FOTC)
------------------------------------------------------------------------------

module FOTC.README where

-- Formalization of (a version of) Azcel's First-Order Theory of
-- Combinators.

------------------------------------------------------------------------------
-- Base axioms
open import FOTC.Base

-- Properties for the base axioms

open import FOTC.Base.PropertiesATP
open import FOTC.Base.PropertiesI

-- Axioms for lists, colists, streams, etc.
open import FOTC.Base.List

-- Properties for axioms for lists, colists, streams, etc

open import FOTC.Base.List.PropertiesATP
open import FOTC.Base.List.PropertiesI

------------------------------------------------------------------------------
-- Booleans

-- The axioms
open import FOTC.Data.Bool

-- The inductive predicate
open import FOTC.Data.Bool.Type

-- Properties
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Bool.PropertiesI

------------------------------------------------------------------------------
-- Natural numbers

-- The axioms
open import FOTC.Data.Nat

-- The inductive predicate
open import FOTC.Data.Nat.Type

-- Properties
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.PropertiesI

open import FOTC.Data.Nat.PropertiesByInductionATP
open import FOTC.Data.Nat.PropertiesByInductionI

-- Divisibility relation
open import FOTC.Data.Nat.Divisibility.By0.PropertiesATP
open import FOTC.Data.Nat.Divisibility.By0.PropertiesI
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI

-- Induction
open import FOTC.Data.Nat.Induction.Acc.WF-I
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI

-- Inequalites
open import FOTC.Data.Nat.Inequalities.EliminationPropertiesATP
open import FOTC.Data.Nat.Inequalities.EliminationPropertiesI
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.Inequalities.PropertiesI

-- Unary numbers
open import FOTC.Data.Nat.UnaryNumbers.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP

------------------------------------------------------------------------------
-- Lists

-- The axioms
open import FOTC.Data.List

-- The inductive predicate
open import FOTC.Data.List.Type

-- Properties
open import FOTC.Data.List.PropertiesATP
open import FOTC.Data.List.PropertiesI

-- Well-founded induction
open import FOTC.Data.List.WF-Relation.LT-Cons.Induction.Acc.WF-I
open import FOTC.Data.List.WF-Relation.LT-Cons.PropertiesI
open import FOTC.Data.List.WF-Relation.LT-Length.Induction.Acc.WF-I
open import FOTC.Data.List.WF-Relation.LT-Length.PropertiesI

------------------------------------------------------------------------------
-- Lists of natural numbers

-- The inductive predicate
open import FOTC.Data.Nat.List

-- Properties
open import FOTC.Data.Nat.List.PropertiesATP
open import FOTC.Data.Nat.List.PropertiesI

------------------------------------------------------------------------------
-- Co-inductive natural numbers

-- The co-inductive predicate
open import FOTC.Data.Conat

-- Properties
open import FOTC.Data.Conat.PropertiesATP
open import FOTC.Data.Conat.PropertiesI

-- Equality
open import FOTC.Data.Conat.Equality

-- Equality properties
open import FOTC.Data.Conat.Equality.PropertiesATP
open import FOTC.Data.Conat.Equality.PropertiesI

------------------------------------------------------------------------------
-- Streams

-- The co-inductive predicate
open import FOTC.Data.Stream

-- Properties
open import FOTC.Data.Stream.PropertiesATP
open import FOTC.Data.Stream.PropertiesI

-- Equality properties
open import FOTC.Data.Stream.Equality.PropertiesATP
open import FOTC.Data.Stream.Equality.PropertiesI

------------------------------------------------------------------------------
-- Bisimilary relation

-- The co-inductive predicate
open import FOTC.Relation.Binary.Bisimilarity

-- Properties
open import FOTC.Relation.Binary.Bisimilarity.PropertiesATP
open import FOTC.Relation.Binary.Bisimilarity.PropertiesI

------------------------------------------------------------------------------
-- Verification of programs

-- Burstall's sort list algorithm: A structurally recursive algorithm
open import FOTC.Program.SortList.SpecificationProofATP
open import FOTC.Program.SortList.SpecificationProofI

-- The division algorithm: A non-structurally recursive algorithm
open import FOTC.Program.Division.SpecificationProofATP
open import FOTC.Program.Division.SpecificationProofI

-- The GCD algorithm: A non-structurally recursive algorithm
open import FOTC.Program.GCD.Partial.SpecificationProofATP
open import FOTC.Program.GCD.Partial.SpecificationProofI
open import FOTC.Program.GCD.Total.SpecificationProofATP
open import FOTC.Program.GCD.Total.SpecificationProofI

-- The nest function: A very simple function with nested recursion
open import FOTC.Program.Nest.PropertiesATP

-- The McCarthy 91 function: A function with nested recursion
open import FOTC.Program.McCarthy91.PropertiesATP

-- The mirror function: A function with higher-order recursion
open import FOTC.Program.Mirror.PropertiesATP
open import FOTC.Program.Mirror.PropertiesI

-- The map-iterate property: A property using co-induction
open import FOTC.Program.MapIterate.MapIterateATP
open import FOTC.Program.MapIterate.MapIterateI

-- The alternating bit protocol: A program using induction and co-induction
open import FOTC.Program.ABP.CorrectnessProofATP
open import FOTC.Program.ABP.CorrectnessProofI

-- The iter₀ function: A partial function
open import FOTC.Program.Iter0.PropertiesATP
open import FOTC.Program.Iter0.PropertiesI

-- The Collatz function: A function without a termination proof
open import FOTC.Program.Collatz.PropertiesATP
open import FOTC.Program.Collatz.PropertiesI
