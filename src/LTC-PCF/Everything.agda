------------------------------------------------------------------------------
-- All the LTC-PCF modules
------------------------------------------------------------------------------

module LTC-PCF.Everything where

open import LTC-PCF.Base
open import LTC-PCF.Base.ConsistencyTest

open import LTC-PCF.Data.Nat
open import LTC-PCF.Data.Nat.Divisibility.NotBy0
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.Properties
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesATP
open import LTC-PCF.Data.Nat.Divisibility.NotBy0.PropertiesI
open import LTC-PCF.Data.Nat.Induction.NonAcc.LexicographicATP
open import LTC-PCF.Data.Nat.Induction.NonAcc.LexicographicI
open import LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionATP
open import LTC-PCF.Data.Nat.Induction.NonAcc.WellFoundedInductionI
open import LTC-PCF.Data.Nat.Inequalities
open import LTC-PCF.Data.Nat.Inequalities.EquationsATP
open import LTC-PCF.Data.Nat.Inequalities.EquationsI
open import LTC-PCF.Data.Nat.Inequalities.PropertiesATP
open import LTC-PCF.Data.Nat.Inequalities.PropertiesI
open import LTC-PCF.Data.Nat.PropertiesATP
open import LTC-PCF.Data.Nat.PropertiesI
open import LTC-PCF.Data.Nat.Rec
open import LTC-PCF.Data.Nat.Rec.EquationsATP
open import LTC-PCF.Data.Nat.Rec.EquationsI

open import LTC-PCF.Fix
open import LTC-PCF.Fix.Properties

open import LTC-PCF.Program.Division.Division
open import LTC-PCF.Program.Division.EquationsATP
open import LTC-PCF.Program.Division.EquationsI
open import LTC-PCF.Program.Division.IsCorrectATP
open import LTC-PCF.Program.Division.IsCorrectI
open import LTC-PCF.Program.Division.ProofSpecificationATP
open import LTC-PCF.Program.Division.ProofSpecificationI
open import LTC-PCF.Program.Division.Specification
open import LTC-PCF.Program.Division.TotalityATP
open import LTC-PCF.Program.Division.TotalityI

open import LTC-PCF.Program.GCD.Partial.Definitions
open import LTC-PCF.Program.GCD.Partial.EquationsATP
open import LTC-PCF.Program.GCD.Partial.EquationsI
open import LTC-PCF.Program.GCD.Partial.GCD
open import LTC-PCF.Program.GCD.Partial.IsCommonDivisorATP
open import LTC-PCF.Program.GCD.Partial.IsCommonDivisorI
open import LTC-PCF.Program.GCD.Partial.IsDivisibleATP
open import LTC-PCF.Program.GCD.Partial.IsDivisibleI
open import LTC-PCF.Program.GCD.Partial.IsGreatestAnyCommonDivisor
open import LTC-PCF.Program.GCD.Partial.IsGreatestAnyCommonDivisor
open import LTC-PCF.Program.GCD.Partial.ProofSpecificationATP
open import LTC-PCF.Program.GCD.Partial.ProofSpecificationI
open import LTC-PCF.Program.GCD.Partial.Specification
open import LTC-PCF.Program.GCD.Partial.TotalityATP
open import LTC-PCF.Program.GCD.Partial.TotalityI

open import LTC-PCF.Relation.Binary.EqReasoning
