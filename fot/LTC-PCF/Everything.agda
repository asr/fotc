------------------------------------------------------------------------------
-- All the LTC-PCF modules
------------------------------------------------------------------------------

module LTC-PCF.Everything where

open import LTC-PCF.Base
open import LTC-PCF.Base.Properties

open import LTC-PCF.Data.Bool
open import LTC-PCF.Data.Bool.Properties
open import LTC-PCF.Data.Bool.Type

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Divisibility.By0
open import LTC-PCF.Data.Nat.Divisibility.By0.Properties
open import LTC-PCF.Data.Nat.Divisibility.NotBy0
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.Properties
open import LTC-PCF.Data.Nat.Induction.NonAcc.Lexicographic
open import LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInduction
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.EliminationProperties
open import LTC-PCF.Data.Nat.Inequalities.Equations
open import LTC-PCF.Data.Nat.Inequalities.Properties
open import LTC-PCF.Data.Nat.Properties
open import LTC-PCF.Data.Nat.Rec
open import LTC-PCF.Data.Nat.Rec.Equations
open import LTC-PCF.Data.Nat.Type

open import LTC-PCF.Loop

open import LTC-PCF.Program.Division.Division
open import LTC-PCF.Program.Division.Equations
open import LTC-PCF.Program.Division.IsCorrect
open import LTC-PCF.Program.Division.ProofSpecification
open import LTC-PCF.Program.Division.Specification
open import LTC-PCF.Program.Division.Totality

open import LTC-PCF.Program.GCD.Partial.CommonDivisor
open import LTC-PCF.Program.GCD.Partial.Definitions
open import LTC-PCF.Program.GCD.Partial.Divisible
open import LTC-PCF.Program.GCD.Partial.Equations
open import LTC-PCF.Program.GCD.Partial.GCD
open import LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor
open import LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor
open import LTC-PCF.Program.GCD.Partial.ProofSpecification
open import LTC-PCF.Program.GCD.Partial.Totality

open import LTC-PCF.Program.GCD.Total.CommonDivisor
open import LTC-PCF.Program.GCD.Total.Definitions
open import LTC-PCF.Program.GCD.Total.Divisible
open import LTC-PCF.Program.GCD.Total.Equations
open import LTC-PCF.Program.GCD.Total.GCD
open import LTC-PCF.Program.GCD.Total.ProofSpecification
open import LTC-PCF.Program.GCD.Total.Totality