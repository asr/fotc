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
-- Natural numberes

-- The axioms
open import LTC-PCF.Data.Nat

-- The inductive predicate
open import LTC-PCF.Data.Nat.Type

-- Properties
open import LTC-PCF.Data.Nat.PropertiesATP
open import LTC-PCF.Data.Nat.PropertiesI

-- Divisibility relation
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.Properties
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesI

-- Induction
open import LTC-PCF.Data.Nat.Induction.NonAcc.LexicographicI
open import LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionI

-- Inequalites
open import LTC-PCF.Data.Nat.Inequalities.EliminationProperties
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI

-- The recursive operator
open import LTC-PCF.Data.Nat.Rec.EquationsATP
open import LTC-PCF.Data.Nat.Rec.EquationsI

------------------------------------------------------------------------------
-- A looping combinator
open import LTC-PCF.Loop

------------------------------------------------------------------------------
-- Verification of programs

-- The division algorithm: A non-structurally recursive algorithm
open import LTC-PCF.Program.Division.ProofSpecificationATP
open import LTC-PCF.Program.Division.ProofSpecificationI

-- The GCD algorithm: A non-structurally recursive algorithm
open import LTC-PCF.Program.GCD.Partial.ProofSpecificationATP
open import LTC-PCF.Program.GCD.Partial.ProofSpecificationI
