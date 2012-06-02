------------------------------------------------------------------------------
-- All the LTC-PCF modules
------------------------------------------------------------------------------

module LTC-PCF.Everything where

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties

open import LTC-PCF.Data.Bool
open import LTC-PCF.Data.Bool.Type

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Divisibility.By0
open import LTC-PCF.Data.Nat.Divisibility.By0.PropertiesI
open import LTC-PCF.Data.Nat.Divisibility.NotBy0
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesI
open import LTC-PCF.Data.Nat.Induction.NonAcc.LexicographicI
open import LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionI
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.EliminationPropertiesI
open import LTC-PCF.Data.Nat.Inequalities.EquationsI
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI
open import LTC-PCF.Data.Nat.PropertiesI
open import LTC-PCF.Data.Nat.Rec
open import LTC-PCF.Data.Nat.Rec.EquationsI
open import LTC-PCF.Data.Nat.Type

open import LTC-PCF.Loop

open import LTC-PCF.Program.Division.Division
open import LTC-PCF.Program.Division.EquationsI
open import LTC-PCF.Program.Division.IsCorrectI
open import LTC-PCF.Program.Division.ProofSpecificationI
open import LTC-PCF.Program.Division.Specification
open import LTC-PCF.Program.Division.TotalityI

open import LTC-PCF.Program.GCD.Partial.CommonDivisorI
open import LTC-PCF.Program.GCD.Partial.Definitions
open import LTC-PCF.Program.GCD.Partial.DivisibleI
open import LTC-PCF.Program.GCD.Partial.EquationsI
open import LTC-PCF.Program.GCD.Partial.GCD
open import LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor
open import LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor
open import LTC-PCF.Program.GCD.Partial.ProofSpecificationI
open import LTC-PCF.Program.GCD.Partial.Specification
open import LTC-PCF.Program.GCD.Partial.TotalityI

open import LTC-PCF.Program.GCD.Total.CommonDivisorI
open import LTC-PCF.Program.GCD.Total.Definitions
open import LTC-PCF.Program.GCD.Total.DivisibleI
open import LTC-PCF.Program.GCD.Total.EquationsI
open import LTC-PCF.Program.GCD.Total.GCD
open import LTC-PCF.Program.GCD.Total.ProofSpecificationI
open import LTC-PCF.Program.GCD.Total.Specification
open import LTC-PCF.Program.GCD.Total.TotalityI
