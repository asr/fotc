------------------------------------------------------------------------------
-- First-Order Theory of Combinators (FOTC)
------------------------------------------------------------------------------

module FOTC.README where

-- Formalization of (a version of) Azcel's First-Order Theory of
-- Combinators.

------------------------------------------------------------------------------
-- The axioms
open import FOTC.Base

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
open import FOTC.Data.Nat.Divisibility.By0.Properties
open import FOTC.Data.Nat.Divisibility.By0.PropertiesATP
open import FOTC.Data.Nat.Divisibility.By0.PropertiesI
open import FOTC.Data.Nat.Divisibility.NotBy0.Properties
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI

-- Induction
open import FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI

-- Inequalites
open import FOTC.Data.Nat.Inequalities.EliminationProperties
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
open import FOTC.Data.List.LT-Cons.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.List.LT-Cons.PropertiesI
open import FOTC.Data.List.LT-Length.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.List.LT-Length.PropertiesI

------------------------------------------------------------------------------
-- Lists of natural numbers

-- The inductive predicate
open import FOTC.Data.Nat.List

-- Properties
open import FOTC.Data.Nat.List.PropertiesATP
open import FOTC.Data.Nat.List.PropertiesI

------------------------------------------------------------------------------
-- Coinductive natural numbers

-- The coinductive predicate
open import FOTC.Data.Conat

-- Equality on coinductive natural numbers
open import FOTC.Data.Conat.Equality

-- Properties
open import FOTC.Data.Conat.PropertiesI

------------------------------------------------------------------------------
-- Streams

-- The coinductive predicate (axioms)
open import FOTC.Data.Stream

-- Properties
open import FOTC.Data.Stream.PropertiesATP
open import FOTC.Data.Stream.PropertiesI

------------------------------------------------------------------------------
-- Bisimilary relation

-- The axioms
open import FOTC.Relation.Binary.Bisimilarity

-- Properties
open import FOTC.Relation.Binary.Bisimilarity.PropertiesATP
open import FOTC.Relation.Binary.Bisimilarity.PropertiesI

------------------------------------------------------------------------------
-- Verification of programs

-- The Collatz function: A function without a termination proof
open import FOTC.Program.Collatz.PropertiesATP
open import FOTC.Program.Collatz.PropertiesI

-- The GCD algorithm: A non-structurally recursive algorithm
open import FOTC.Program.GCD.Partial.ProofSpecificationATP
open import FOTC.Program.GCD.Partial.ProofSpecificationI
open import FOTC.Program.GCD.Total.ProofSpecificationATP
open import FOTC.Program.GCD.Total.ProofSpecificationI

-- The McCarthy 91 function: A function with nested recursion
open import FOTC.Program.McCarthy91.PropertiesATP

-- The mirror function: A function with higher-order recursion
open import FOTC.Program.Mirror.PropertiesATP
open import FOTC.Program.Mirror.PropertiesI

-- Burstall's sort list algorithm: A structurally recursive algorithm
open import FOTC.Program.SortList.ProofSpecificationATP
open import FOTC.Program.SortList.ProofSpecificationI

-- The division algorithm: A non-structurally recursive algorithm
open import FOTC.Program.Division.ProofSpecificationATP
open import FOTC.Program.Division.ProofSpecificationI

-- The map-iterate property: A property using co-induction
open import FOTC.Program.MapIterate.MapIterateATP
open import FOTC.Program.MapIterate.MapIterateI

-- The alternating bit protocol: A program using induction and co-induction
open import FOTC.Program.ABP.ProofSpecificationATP
open import FOTC.Program.ABP.ProofSpecificationI
