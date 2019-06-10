------------------------------------------------------------------------------
-- First-Order Theory of Combinators (FOTC)
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- Code accompanying the paper "Combining Interactive and Automatic
-- Reasoning in First Order Theories of Functional Programs" by Ana
-- Bove, Peter Dybjer and Andrés Sicard-Ramírez (FoSSaCS 2012).

-- The code presented here does not match the paper exactly.

module Combined.FOTC.README where

------------------------------------------------------------------------------
-- Description

-- Verification of functional programs using a version of Azcel's
-- First-Order Theory of Combinators and showing the combination of
-- interactive proofs with automatics proofs carried out by
-- first-order automatic theorem provers (ATPs).

------------------------------------------------------------------------------
-- For the paper, prerequisites, tested versions of the ATPs and use,
-- see https://github.com/asr/fotc/.

------------------------------------------------------------------------------
-- Conventions

-- If the module's name ends in 'I' the module contains interactive
-- proofs, if it ends in 'ATP' the module contains combined proofs,
-- otherwise the module contains definitions and/or interactive proofs
-- that are used by the interactive and combined proofs.

------------------------------------------------------------------------------
-- Base axioms
open import Combined.FOTC.Base

-- Properties for the base axioms

open import Combined.FOTC.Base.Properties

-- Axioms for lists, colists, streams, etc.
open import Combined.FOTC.Base.List

-- Properties for axioms for lists, colists, streams, etc
open import Combined.FOTC.Base.List.Properties

------------------------------------------------------------------------------
-- Booleans

-- The axioms
open import Combined.FOTC.Data.Bool

-- The inductive predicate
open import Combined.FOTC.Data.Bool.Type

-- Properties
open import Combined.FOTC.Data.Bool.Properties


------------------------------------------------------------------------------
-- Natural numbers

-- The axioms
open import Combined.FOTC.Data.Nat

-- The inductive predicate
open import Combined.FOTC.Data.Nat.Type

-- Properties
open import Combined.FOTC.Data.Nat.Properties
open import Combined.FOTC.Data.Nat.PropertiesByInduction

-- Divisibility relation
open import Combined.FOTC.Data.Nat.Divisibility.By0.Properties
open import Combined.FOTC.Data.Nat.Divisibility.NotBy0.Properties

-- Induction
open import Combined.FOTC.Data.Nat.Induction.Acc.WF
open import Combined.FOTC.Data.Nat.Induction.NonAcc.Lexicographic

-- Inequalites
open import Combined.FOTC.Data.Nat.Inequalities.EliminationProperties
open import Combined.FOTC.Data.Nat.Inequalities.Properties

-- Unary numbers
open import Combined.FOTC.Data.Nat.UnaryNumbers.Inequalities.Properties
open import Combined.FOTC.Data.Nat.UnaryNumbers.Totality

------------------------------------------------------------------------------
-- Lists

-- The axioms
open import Combined.FOTC.Data.List

-- The inductive predicate
open import Combined.FOTC.Data.List.Type

-- Properties
open import Combined.FOTC.Data.List.Properties

-- Well-founded induction
open import Combined.FOTC.Data.List.WF-Relation.LT-Cons.Induction.Acc.WF
open import Combined.FOTC.Data.List.WF-Relation.LT-Cons.Properties
open import Combined.FOTC.Data.List.WF-Relation.LT-Length.Induction.Acc.WF
open import Combined.FOTC.Data.List.WF-Relation.LT-Length.Properties

------------------------------------------------------------------------------
-- Lists of natural numbers

-- The inductive predicate
open import Combined.FOTC.Data.Nat.List

-- Properties
open import Combined.FOTC.Data.Nat.List.Properties

------------------------------------------------------------------------------
-- Co-inductive natural numbers

-- Some axioms
open import Combined.FOTC.Data.Conat

-- The co-inductive predicate
open import Combined.FOTC.Data.Conat.Type

-- Properties
open import Combined.FOTC.Data.Conat.Properties

-- Equality
open import Combined.FOTC.Data.Conat.Equality.Type

-- Equality properties
open import Combined.FOTC.Data.Conat.Equality.Properties

------------------------------------------------------------------------------
-- Streams

-- Some axioms
open import Combined.FOTC.Data.Stream

-- The co-inductive predicate
open import Combined.FOTC.Data.Stream.Type

-- Properties
open import Combined.FOTC.Data.Stream.Properties

-- Equality properties
open import Combined.FOTC.Data.Stream.Equality.Properties

------------------------------------------------------------------------------
-- Bisimilary relation

-- The co-inductive predicate
open import Combined.FOTC.Relation.Binary.Bisimilarity.Type

-- Properties
open import Combined.FOTC.Relation.Binary.Bisimilarity.Properties

------------------------------------------------------------------------------
-- Verification of programs

-- Burstall's sort list algorithm: A structurally recursive algorithm
open import Combined.FOTC.Program.SortList.CorrectnessProof

-- The division algorithm: A non-structurally recursive algorithm
open import Combined.FOTC.Program.Division.CorrectnessProof

-- The GCD algorithm: A non-structurally recursive algorithm
open import Combined.FOTC.Program.GCD.Partial.CorrectnessProof
open import Combined.FOTC.Program.GCD.Total.CorrectnessProof

-- The nest function: A very simple function with nested recursion
open import Combined.FOTC.Program.Nest.Properties

-- The McCarthy 91 function: A function with nested recursion
open import Combined.FOTC.Program.McCarthy91.Properties

-- The mirror function: A function with higher-order recursion
open import Combined.FOTC.Program.Mirror.Properties

-- The map-iterate property: A property using co-induction
open import Combined.FOTC.Program.MapIterate.MapIterate

-- The alternating bit protocol: A program using induction and co-induction
open import Combined.FOTC.Program.ABP.CorrectnessProof

-- The iter₀ function: A partial function
open import Combined.FOTC.Program.Iter0.Properties

-- The Collatz function: A function without a termination proof
open import Combined.FOTC.Program.Collatz.Properties
