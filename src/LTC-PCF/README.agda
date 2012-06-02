------------------------------------------------------------------------------
-- Logical Theory of Constructions for PCF (LTC-PCF)
------------------------------------------------------------------------------

module LTC-PCF.README where

-- Formalization of (a version of) Azcel's Logical Theory of
-- Constructions for PCF.
--
-- (This was the theory shown in our PLPV'09 paper)

------------------------------------------------------------------------------
-- The axioms
open import LTC-PCF.Base

------------------------------------------------------------------------------
-- Booleans

-- The inductive predicate
open import FOTC.Data.Bool.Type

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
