------------------------------------------------------------------------------
-- FOT (First Order Theories)
------------------------------------------------------------------------------

-- Code accompanying the paper "Combining Automatic and Interactive
-- Proof in First Order Theories of Combinators" by Ana Bove,
-- Peter Dybjer, and Andrés Sicard-Ramírez.

------------------------------------------------------------------------------

module README where

------------------------------------------------------------------------------
-- Description
------------------------------------------------------------------------------

-- Examples of the formalization of first order theories showing the
-- combination of interactive proofs with automatics proofs carried
-- out by first order automatic theorem provers (ATPs).

------------------------------------------------------------------------------
-- Prerequisites
------------------------------------------------------------------------------

-- You can download the agda2atp tool (described in above paper) using
-- darcs with the following command:

-- $ darcs get http://patch-tag.com/r/asr/agda2atp

-- The agda2atp tool and the FOT code require a modified version of
-- Agda. See agda2atp/README.txt for the related instructions.

------------------------------------------------------------------------------
-- Use
------------------------------------------------------------------------------

-- Let's suppose you want to use the Metis ATP to prove the group
-- theory properties stated in the module
-- GroupTheory.PropertiesATP. First, you should type-check the module using
-- Agda

-- $ agda -isrc src/GroupTheory/PropertiesATP.agda

-- Second, you call the agda2tool using the Metis ATP

-- $ agda2atp -isrc --atp=metis src/GroupTheory/PropertiesATP.agda

------------------------------------------------------------------------------
-- First order theories
------------------------------------------------------------------------------

-- Conventions

-- The following modules show the formalization of some first order
-- theories. If the module's name ends in 'I' the module contains
-- interactive proofs, if it ends in 'ATP' the module contains
-- combined proofs, otherwise the module contains interactive proofs
-- that are used by the combined proofs.

------------------------------------------------------------------------------
-- Distributive laws on a binary operation

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

open import DistributiveLaws.TaskB-HalvedStepsATP
open import DistributiveLaws.TaskB-I
open import DistributiveLaws.TaskB-TopDownATP

------------------------------------------------------------------------------
-- Group theory

-- We formalize the theory of groups using Agda postulates for
-- the group axioms.

-- Basic properties
open import GroupTheory.PropertiesATP
open import GroupTheory.PropertiesI

-- Commutator properties
open import GroupTheory.Commutator.PropertiesATP
open import GroupTheory.Commutator.PropertiesI

-- Abelian groups
open import GroupTheory.AbelianGroup.PropertiesATP

------------------------------------------------------------------------------
-- Logic

-- Propositional logic
open import Logic.Propositional.PropertiesATP
open import Logic.Predicate.PropertiesI

-- Predicate logic
open import Logic.Predicate.PropertiesATP
open import Logic.Predicate.PropertiesI

-- Logical schemas
open import Logic.SchemasATP

------------------------------------------------------------------------------
-- FOTC

-- Formalization of (a version of) Azcel's First Order Theory of Combinators.

-- FOTC base
open import FOTC.Base.Properties
open import FOTC.Base.PropertiesATP
open import FOTC.Base.PropertiesI

-- Booleans
open import FOTC.Data.Bool.PropertiesATP
open import FOTC.Data.Bool.PropertiesI

-- Lists: Common properties
open import FOTC.Data.List.Length.PropertiesATP
open import FOTC.Data.List.Length.PropertiesI
open import FOTC.Data.List.PropertiesATP
open import FOTC.Data.List.PropertiesI

-- Lists: Well-founded induction
open import FOTC.Data.List.LT-Cons.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.List.LT-Cons.PropertiesI
open import FOTC.Data.List.LT-Length.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.List.LT-Length.PropertiesI

-- Naturals numbers: Common properties
open import FOTC.Data.Nat.PropertiesATP
open import FOTC.Data.Nat.PropertiesI

open import FOTC.Data.Nat.PropertiesByInductionATP
open import FOTC.Data.Nat.PropertiesByInductionI

-- Naturals numbers: Divisibility relation
open import FOTC.Data.Nat.Divisibility.PropertiesATP
open import FOTC.Data.Nat.Divisibility.PropertiesI

-- Naturals numbers: Induction
open import FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI
open import FOTC.Data.Nat.Induction.NonAcc.LexicographicI

-- Naturals numbers: Inequalites
open import FOTC.Data.Nat.Inequalities.PropertiesATP
open import FOTC.Data.Nat.Inequalities.PropertiesI

-- Naturals numbers: List
open import FOTC.Data.Nat.List.PropertiesATP
open import FOTC.Data.Nat.List.PropertiesI

-- Naturals numbers: Unary numbers
open import FOTC.Data.Nat.UnaryNumbers.IsN-ATP
open import FOTC.Data.Nat.UnaryNumbers.Inequalities.PropertiesATP

-- Induction
open import FOTC.Induction.WellFounded

-- The Collatz function: A function without a termination proof
open import FOTC.Program.Collatz.PropertiesATP
open import FOTC.Program.Collatz.PropertiesI

-- The GCD algorithm: A non-structurally recursive algorithm
open import FOTC.Program.GCD.ProofSpecificationATP
open import FOTC.Program.GCD.ProofSpecificationI

-- The McCarthy 91 function: A function with nested recursion
open import FOTC.Program.McCarthy91.Properties.MainATP

-- The mirror function: A function with higher-order recursion
open import FOTC.Program.Mirror.PropertiesATP
open import FOTC.Program.Mirror.PropertiesI

-- Burstall's sort list algorithm: A structurally recursive algorithm
open import FOTC.Program.SortList.ProofSpecificationATP
open import FOTC.Program.SortList.ProofSpecificationI

------------------------------------------------------------------------------
-- LTC-PCF

-- Formalization of a version of Azcel's Logical Theory of Constructions.

-- Naturals numbers: Common properties
open import LTC-PCF.Data.Nat.PropertiesATP
open import LTC-PCF.Data.Nat.PropertiesI

-- Naturals numbers: Divisibility relation
open import LTC-PCF.Data.Nat.Divisibility.Properties
open import LTC-PCF.Data.Nat.Divisibility.PropertiesATP
open import LTC-PCF.Data.Nat.Divisibility.PropertiesI

-- Naturals numbers: Induction
open import LTC-PCF.Data.Nat.Induction.NonAcc.LexicographicI
open import LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionI

-- Naturals numbers: Inequalites
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI

-- Naturals numbers: The recursive operator
open import LTC-PCF.Data.Nat.Rec.EquationsATP
open import LTC-PCF.Data.Nat.Rec.EquationsI

-- The division algorithm: A non-structurally recursive algorithm
open import LTC-PCF.Program.Division.ProofSpecificationATP
open import LTC-PCF.Program.Division.ProofSpecificationI

-- The GCD algorithm: A non-structurally recursive algorithm
open import LTC-PCF.Program.GCD.ProofSpecificationATP
open import LTC-PCF.Program.GCD.ProofSpecificationI

------------------------------------------------------------------------------
-- Peano arithmetic (PA)

-- We write two formalizations of PA. In the axiomatic formalization
-- we use Agda postulates for Peano's axioms. In the inductive
-- formalization, we use Agda data types and primitive recursive
-- functions.

-- Axiomatic PA
open import PA.Axiomatic.PropertiesATP
open import PA.Axiomatic.PropertiesI

open import PA.Axiomatic.Relation.Binary.PropositionalEqualityATP
open import PA.Axiomatic.Relation.Binary.PropositionalEqualityI

-- Inductive PA
open import PA.Inductive.Properties
open import PA.Inductive.PropertiesATP
open import PA.Inductive.PropertiesI

open import PA.Inductive.PropertiesByInduction
open import PA.Inductive.PropertiesByInductionATP
open import PA.Inductive.PropertiesByInductionI

------------------------------------------------------------------------------
-- ATPs failures
------------------------------------------------------------------------------

-- The ATPs (E, Equinox, Metis and Vampire) could not prove some
-- theorems.

open import DistributiveLaws.TaskB-ATP
open import LTC-PCF.Program.GCD.EquationsATP
open import PA.Axiomatic.PropertiesATP

------------------------------------------------------------------------------
-- Agsy examples
------------------------------------------------------------------------------

-- We cannot import the Agsy examples because some modules contain
-- unsolved metas, therefore see src/Agsy/README.txt
