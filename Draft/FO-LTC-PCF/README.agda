------------------------------------------------------------------------------
-- Logical Theory of Constructions for PCF (LTC-PCF)
------------------------------------------------------------------------------

module Draft.FO-LTC-PCF.README where

-- Formalization of (a version of) Azcel's Logical Theory of
-- Constructions for PCF.
--
-- (This was the theory shown in our PLPV'09 paper)

------------------------------------------------------------------------------
-- The axioms
open import Draft.FO-LTC-PCF.Base

------------------------------------------------------------------------------
-- Natural numberes

-- The axioms
open import Draft.FO-LTC-PCF.Data.Nat

-- The inductive predicate
open import Draft.FO-LTC-PCF.Data.Nat.Type

-- Properties
open import Draft.FO-LTC-PCF.Data.Nat.PropertiesATP
open import Draft.FO-LTC-PCF.Data.Nat.PropertiesI

-- Divisibility relation
open import Draft.FO-LTC-PCF.Data.Nat.Divisibility.NotBy0.Properties
open import Draft.FO-LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import Draft.FO-LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesI

-- Induction
open import Draft.FO-LTC-PCF.Data.Nat.Induction.NonAcc.LexicographicI
open import Draft.FO-LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionI

-- Inequalites
open import Draft.FO-LTC-PCF.Data.Nat.Inequalities.EliminationPropertiesATP
open import Draft.FO-LTC-PCF.Data.Nat.Inequalities.EliminationPropertiesI
open import Draft.FO-LTC-PCF.Data.Nat.Inequalities.PropertiesATP
open import Draft.FO-LTC-PCF.Data.Nat.Inequalities.PropertiesI

-- The recursive operator
open import Draft.FO-LTC-PCF.Data.Nat.Rec.EquationsATP
open import Draft.FO-LTC-PCF.Data.Nat.Rec.EquationsI

------------------------------------------------------------------------------
-- A looping combinator
open import Draft.FO-LTC-PCF.Loop

------------------------------------------------------------------------------
-- Verification of programs

-- The division algorithm: A non-structurally recursive algorithm
open import Draft.FO-LTC-PCF.Program.Division.ProofSpecificationATP
open import Draft.FO-LTC-PCF.Program.Division.ProofSpecificationI

-- The GCD algorithm: A non-structurally recursive algorithm
open import Draft.FO-LTC-PCF.Program.GCD.Partial.ProofSpecificationATP
open import Draft.FO-LTC-PCF.Program.GCD.Partial.ProofSpecificationI
