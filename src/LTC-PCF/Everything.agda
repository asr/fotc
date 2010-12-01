------------------------------------------------------------------------------
-- All the LTC-PCF modules
------------------------------------------------------------------------------

module LTC-PCF.Everything where

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Divisibility
open import LTC-PCF.Data.Nat.Divisibility.Properties
open import LTC-PCF.Data.Nat.Induction.Lexicographic
open import LTC-PCF.Data.Nat.Induction.WellFounded
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.Properties
open import LTC-PCF.Data.Nat.Properties
open import LTC-PCF.Data.Nat.Rec
open import LTC-PCF.Data.Nat.Rec.Equations

open import LTC-PCF.Program.Division.Division
open import LTC-PCF.Program.Division.Equations
open import LTC-PCF.Program.Division.IsCorrect
open import LTC-PCF.Program.Division.IsN
open import LTC-PCF.Program.Division.ProofSpecification
open import LTC-PCF.Program.Division.Specification

open import LTC-PCF.Program.GCD.Equations
open import LTC-PCF.Program.GCD.GCD
open import LTC-PCF.Program.GCD.IsCommonDivisor
open import LTC-PCF.Program.GCD.IsDivisible
open import LTC-PCF.Program.GCD.IsGreatestAnyCommonDivisor
open import LTC-PCF.Program.GCD.IsN
open import LTC-PCF.Program.GCD.ProofSpecification
