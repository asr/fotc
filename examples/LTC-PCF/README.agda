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
open import LTC-PCF.Data.Bool.PropertiesI

------------------------------------------------------------------------------
-- Natural numberes

-- The arithmetical functions
open import LTC-PCF.Data.Nat

-- The inductive predicate
open import LTC-PCF.Data.Nat.Type

-- Properties
open import LTC-PCF.Data.Nat.PropertiesI

-- Divisibility relation
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesI

-- Induction
open import LTC-PCF.Data.Nat.Induction.NonAcc.LexicographicI
open import LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionI

-- Inequalites
open import LTC-PCF.Data.Nat.Inequalities.EliminationPropertiesI
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI

-- The recursive operator
open import LTC-PCF.Data.Nat.Rec.EquationsI

------------------------------------------------------------------------------
-- A looping combinator
open import LTC-PCF.Loop

------------------------------------------------------------------------------
-- Verification of programs

-- The division algorithm: A non-structurally recursive algorithm
open import LTC-PCF.Program.Division.ProofSpecificationI

-- The GCD algorithm: A non-structurally recursive algorithm
open import LTC-PCF.Program.GCD.Partial.ProofSpecificationI
open import LTC-PCF.Program.GCD.Total.ProofSpecificationI
