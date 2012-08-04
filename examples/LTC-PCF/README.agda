------------------------------------------------------------------------------
-- Logical Theory of Constructions for PCF (LTC-PCF)
------------------------------------------------------------------------------

module LTC-PCF.README where

-- Code accompanying the paper "Embedding a Logical Theory of
-- Constructions in Agda" by Ana Bove, Peter Dybjer, and Andrés
-- Sicard-Ramírez (PLPV'09).

-- The code presented here does not match the paper exactly.

-- Formalization of (a version of) Azcel's Logical Theory of
-- Constructions for PCF.

-- The code has been tested with Agda 2.3.0.1.

------------------------------------------------------------------------------
-- The axioms
open import LTC-PCF.Base

------------------------------------------------------------------------------
-- Booleans

-- The inductive predicate
open import LTC-PCF.Data.Bool.Type

-- Properties
open import LTC-PCF.Data.Bool.Properties

------------------------------------------------------------------------------
-- Natural numberes

-- The arithmetical functions
open import LTC-PCF.Data.Nat

-- The inductive predicate
open import LTC-PCF.Data.Nat.Type

-- Properties
open import LTC-PCF.Data.Nat.Properties

-- Divisibility relation
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.Properties

-- Induction
open import LTC-PCF.Data.Nat.Induction.NonAcc.Lexicographic
open import LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInduction

-- Inequalites
open import LTC-PCF.Data.Nat.Inequalities.EliminationProperties
open import LTC-PCF.Data.Nat.Inequalities.Properties

-- The recursive operator
open import LTC-PCF.Data.Nat.Rec.Equations

------------------------------------------------------------------------------
-- A looping combinator
open import LTC-PCF.Loop

------------------------------------------------------------------------------
-- Verification of programs

-- The division algorithm: A non-structurally recursive algorithm
open import LTC-PCF.Program.Division.ProofSpecification

-- The GCD algorithm: A non-structurally recursive algorithm
open import LTC-PCF.Program.GCD.Partial.ProofSpecification
open import LTC-PCF.Program.GCD.Total.ProofSpecification
