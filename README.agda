------------------------------------------------------------------------------
-- FOT (First Order Theories)
------------------------------------------------------------------------------

-- Code accompanying the paper "Combining Interactive and Automatic
-- Reasoning about Functional Programs" by Ana Bove, Peter Dybjer, and
-- Andrés Sicard-Ramírez.

------------------------------------------------------------------------------

module README where

------------------------------------------------------------------------------
-- Description
------------------------------------------------------------------------------

-- Examples of the formalization of first order theories showing the
-- combination of interactive proofs with automatics proofs carried
-- out by first order automatic theorem provers (ATPs).

------------------------------------------------------------------------------
-- Prerequisites and use
------------------------------------------------------------------------------

-- See http://www1.eafit.edu.co/asicard/code/fotc/.

------------------------------------------------------------------------------
-- First order theories
------------------------------------------------------------------------------

-- Conventions

-- The following modules show the formalization of some first order
-- theories. If the module's name ends in 'I' the module contains
-- interactive proofs, if it ends in 'ATP' the module contains
-- combined proofs, otherwise the module contains definions and/or
-- interactive proofs that are used by the interactive and combined
-- proofs.

------------------------------------------------------------------------------
-- 1. Predicate logic

-- 1.1 Definition of the connectives and quantifiers
open import Common.LogicalConstants
open import PredicateLogic.Constants

-- 1.2 The law of the excluded middle
open import PredicateLogic.ClassicalATP

-- 1.3 Non-empty domains
open import PredicateLogic.NonEmptyDomain.TheoremsATP
open import PredicateLogic.NonEmptyDomain.TheoremsI

-- 1.4 Logical schemas
open import PredicateLogic.SchemasATP

-- 1.5 Propositional logic theorems
open import PredicateLogic.Propositional.TheoremsATP
open import PredicateLogic.Propositional.TheoremsI

-- 1.6 Predicate logic theorems
open import PredicateLogic.TheoremsATP
open import PredicateLogic.TheoremsI

------------------------------------------------------------------------------
-- 2. Equality

-- 2.1 Definition of equality and some properties about it
open import Common.Relation.Binary.PropositionalEquality

-- 2.2 The equality reasoning
open import Common.Relation.Binary.PreorderReasoning

------------------------------------------------------------------------------
-- 3. Group theory

-- 3.1 The axioms
open import GroupTheory.Base

-- 3.2 Basic properties
open import GroupTheory.PropertiesATP
open import GroupTheory.PropertiesI

-- 3.3 Commutator properties
open import GroupTheory.Commutator.PropertiesATP
open import GroupTheory.Commutator.PropertiesI

-- 3.4 Abelian groups
open import GroupTheory.AbelianGroup.PropertiesATP

------------------------------------------------------------------------------
-- 4. Stanovský example (distributive laws on a binary operation)

-- We prove the proposition 2 (task B) of [1]. Let _·_ be a
-- left-associative binary operation, the task B consist in given the
-- left and right distributive axioms

--   ∀ x y z → x ∙ (y ∙ z) ≡ (x ∙ y) ∙ (x ∙ z)
--   ∀ x y z → (x ∙ y) ∙ z ≡ (x ∙ z) ∙ (y ∙ z)

-- to prove the theorem

--   ∀ u x y z → (x ∙ y ∙ (z ∙ u)) ∙
--               (( x ∙ y ∙ ( z ∙ u)) ∙ (x ∙ z ∙ (y ∙ u))) ≡
--               x ∙ z ∙ (y ∙ u)

-- [1] David Stanovský. Distributive groupoids are symmetrical-by-medial:
--     An elementary proof. Commentations Mathematicae Universitatis
--     Carolinae, 49(4):541–546, 2008.

-- 4.1 The ATPs could not prove the theorem
open import DistributiveLaws.TaskB-ATP

-- 4.2 The interactive and combined proofs
open import DistributiveLaws.TaskB-HalvedStepsATP
open import DistributiveLaws.TaskB-I
open import DistributiveLaws.TaskB-TopDownATP

------------------------------------------------------------------------------
-- 5. Peano arithmetic (PA)

-- We write two formalizations of PA. In the axiomatic formalization
-- we use Agda postulates for Peano's axioms. In the inductive
-- formalization, we use Agda data types and primitive recursive
-- functions.

-- 5.1 Axiomatic PA
-- 5.1.1 The axioms
open import PA.Axiomatic.Base

-- 5.1.2 Some properties
open import PA.Axiomatic.PropertiesATP
open import PA.Axiomatic.PropertiesI

open import PA.Axiomatic.Relation.Binary.PropositionalEqualityATP
open import PA.Axiomatic.Relation.Binary.PropositionalEqualityI

-- 5.2. Inductive PA
-- 5.2.1 Some properties
open import PA.Inductive.Properties
open import PA.Inductive.PropertiesATP
open import PA.Inductive.PropertiesI

open import PA.Inductive.PropertiesByInduction
open import PA.Inductive.PropertiesByInductionATP
open import PA.Inductive.PropertiesByInductionI

------------------------------------------------------------------------------
-- 6. FOTC

-- Formalization of (a version of) Azcel's First Order Theory of Combinators.

-- 6.1 The axioms
open import FOTC.Base

-- 6.2 Booleans

-- 6.2.1 The axioms
open import FOTC.Data.Bool

-- 6.2.2 The inductive predicate
open import FOTC.Data.Bool.Type

-- 6.2.3 Properties
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Bool.PropertiesI

-- 6.3. Natural numbers

-- 6.3.1 The axioms
open import FOTC.Data.Nat

-- 6.3.2 The inductive predicate
open import FOTC.Data.Nat.Type

-- 6.3.3 Properties
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.PropertiesI

open import FOTC.Data.Nat.PropertiesByInductionATP
open import FOTC.Data.Nat.PropertiesByInductionI

-- 6.3.4 Divisibility relation
open import FOTC.Data.Nat.Divisibility.By0.Properties
open import FOTC.Data.Nat.Divisibility.By0.PropertiesATP
open import FOTC.Data.Nat.Divisibility.By0.PropertiesI
open import FOTC.Data.Nat.Divisibility.NotBy0.Properties
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import FOTC.Data.Nat.Divisibility.NotBy0.PropertiesI

-- 6.3.5 Induction
open import FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI

-- 6.3.6 Inequalites
open import FOTC.Data.Nat.Inequalities.Properties
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.Inequalities.PropertiesI

-- 6.3.7 Unary numbers
open import FOTC.Data.Nat.UnaryNumbers.Inequalities.PropertiesATP
open import FOTC.Data.Nat.UnaryNumbers.TotalityATP

-- 6.4 Lists

-- 6.4.1 The axioms
open import FOTC.Data.List

-- 6.4.2 The inductive predicate
open import FOTC.Data.List.Type

-- 6.4.3 Properties
open import FOTC.Data.List.PropertiesATP
open import FOTC.Data.List.PropertiesI

-- 6.4.4 Well-founded induction
open import FOTC.Data.List.LT-Cons.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.List.LT-Cons.PropertiesI
open import FOTC.Data.List.LT-Length.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.List.LT-Length.PropertiesI

-- 6.4.5 Lists of natural numbers

-- 6.4.5.1 The inductive predicate
open import FOTC.Data.Nat.List.Type

-- 6.4.5.2 Properties
open import FOTC.Data.Nat.List.PropertiesATP
open import FOTC.Data.Nat.List.PropertiesI

-- 6.5 Streams

-- 6.5.1 The coinductive predicate (axioms)
open import FOTC.Data.Stream

-- 6.5.2 Equality on streams
open import FOTC.Data.Stream.Equality
open import FOTC.Data.Stream.Equality.PropertiesATP
open import FOTC.Data.Stream.Equality.PropertiesI

-- 6.5.3 Properties
open import FOTC.Data.Stream.PropertiesATP
open import FOTC.Data.Stream.PropertiesI

-- 6.7 Programs

-- 6.7.1 The Collatz function: A function without a termination proof
open import FOTC.Program.Collatz.PropertiesATP
open import FOTC.Program.Collatz.PropertiesI

-- 6.7.2 The GCD algorithm: A non-structurally recursive algorithm
open import FOTC.Program.GCD.Partial.ProofSpecificationATP
open import FOTC.Program.GCD.Partial.ProofSpecificationI
open import FOTC.Program.GCD.Total.ProofSpecificationATP
open import FOTC.Program.GCD.Total.ProofSpecificationI

-- 6.7.3 The McCarthy 91 function: A function with nested recursion
open import FOTC.Program.McCarthy91.Properties.MainATP

-- 6.7.4 The mirror function: A function with higher-order recursion
open import FOTC.Program.Mirror.PropertiesATP
open import FOTC.Program.Mirror.PropertiesI

-- 6.7.5 Burstall's sort list algorithm: A structurally recursive algorithm
open import FOTC.Program.SortList.ProofSpecificationATP
open import FOTC.Program.SortList.ProofSpecificationI

-- 6.7.6 The division algorithm: A non-structurally recursive algorithm
open import FOTC.Program.Division.ProofSpecificationATP
open import FOTC.Program.Division.ProofSpecificationI

-- 6.7.7 The map-iterate property: A property using coinduction
open import FOTC.Program.MapIterate.MapIterateATP

-- 6.7.8 The alternating bit protocol: A program using co-inductive types
open import FOTC.Program.ABP.ProofSpecificationATP
open import FOTC.Program.ABP.ProofSpecificationI

-- 6.8 Other modules
-- (These modules are not imported from any module).
open import FOTC.Program.Division.EquationsATP
open import FOTC.Program.GCD.Partial.EquationsATP
open import FOTC.Program.GCD.Total.EquationsATP

------------------------------------------------------------------------------
-- ATPs failures
------------------------------------------------------------------------------

-- The ATPs (E, Equinox, Metis, SPASS and Vampire) could not prove some
-- theorems.

open import DistributiveLaws.TaskB-ATP
open import FOTC.Program.ABP.MayorPremiseATP
open import PA.Axiomatic.PropertiesATP

------------------------------------------------------------------------------
-- Agsy examples
------------------------------------------------------------------------------

-- We cannot import the Agsy examples because some modules contain
-- unsolved metas, therefore see src/Agsy/README.txt

------------------------------------------------------------------------------
-- Other theories
------------------------------------------------------------------------------

-- 1. LTC-PCF
-- Formalization of a version of Azcel's Logical Theory of Constructions.
-- N.B. This was the theory shown in our PLPV'09 paper.

-- 1.1. The axioms
open import LTC-PCF.Base

-- 1.2 Natural numberes

-- 1.2.1 The axioms
open import LTC-PCF.Data.Nat

-- 1.2.2 Properties
open import LTC-PCF.Data.Nat.PropertiesATP
open import LTC-PCF.Data.Nat.PropertiesI

-- 1.2.3 Divisibility relation
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.Properties
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesI

-- 1.2.4 Induction
open import LTC-PCF.Data.Nat.Induction.NonAcc.LexicographicI
open import LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionI

-- 1.2.5 Inequalites
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI

-- 1.2.6 The recursive operator
open import LTC-PCF.Data.Nat.Rec.EquationsATP
open import LTC-PCF.Data.Nat.Rec.EquationsI

-- 1.3 Programs

-- 1.3.1 The division algorithm: A non-structurally recursive algorithm
open import LTC-PCF.Program.Division.ProofSpecificationATP
open import LTC-PCF.Program.Division.ProofSpecificationI

-- 1.3.2 The GCD algorithm: A non-structurally recursive algorithm
open import LTC-PCF.Program.GCD.Partial.ProofSpecificationATP
open import LTC-PCF.Program.GCD.Partial.ProofSpecificationI
