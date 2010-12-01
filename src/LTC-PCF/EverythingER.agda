------------------------------------------------------------------------------
-- All the LTC-PCF properties and programs using equational reasoning
------------------------------------------------------------------------------

module LTC-PCF.EverythingER where

open import LTC-PCF.Data.Nat.Divisibility.PropertiesER
open import LTC-PCF.Data.Nat.Inequalities.PropertiesER
open import LTC-PCF.Data.Nat.PropertiesER
open import LTC-PCF.Data.Nat.Rec.EquationsER

open import LTC-PCF.Program.Division.EquationsER
open import LTC-PCF.Program.Division.IsCorrectER
open import LTC-PCF.Program.Division.IsN-ER
open import LTC-PCF.Program.Division.ProofSpecificationER

open import LTC-PCF.Program.GCD.EquationsER
open import LTC-PCF.Program.GCD.IsCommonDivisorER
open import LTC-PCF.Program.GCD.IsDivisibleER
open import LTC-PCF.Program.GCD.IsGreatestAnyCommonDivisorER
open import LTC-PCF.Program.GCD.IsN-ER
open import LTC-PCF.Program.GCD.ProofSpecificationER
