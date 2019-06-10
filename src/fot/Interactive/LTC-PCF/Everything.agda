------------------------------------------------------------------------------
-- All the Interactive.LTC-PCF modules
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.LTC-PCF.Everything where

open import Interactive.LTC-PCF.Base
open import Interactive.LTC-PCF.Base.Properties

open import Interactive.LTC-PCF.Data.Bool
open import Interactive.LTC-PCF.Data.Bool.Properties
open import Interactive.LTC-PCF.Data.Bool.Type

open import Interactive.LTC-PCF.Data.Nat
open import Interactive.LTC-PCF.Data.Nat.Divisibility.By0
open import Interactive.LTC-PCF.Data.Nat.Divisibility.By0.Properties
open import Interactive.LTC-PCF.Data.Nat.Divisibility.NotBy0
open import Interactive.LTC-PCF.Data.Nat.Divisibility.NotBy0.Properties
open import Interactive.LTC-PCF.Data.Nat.Induction.NonAcc.Lexicographic
open import Interactive.LTC-PCF.Data.Nat.Induction.NonAcc.WF
open import Interactive.LTC-PCF.Data.Nat.Inequalities
open import Interactive.LTC-PCF.Data.Nat.Inequalities.ConversionRules
open import Interactive.LTC-PCF.Data.Nat.Inequalities.EliminationProperties
open import Interactive.LTC-PCF.Data.Nat.Inequalities.Properties
open import Interactive.LTC-PCF.Data.Nat.Properties
open import Interactive.LTC-PCF.Data.Nat.Rec
open import Interactive.LTC-PCF.Data.Nat.Rec.ConversionRules
open import Interactive.LTC-PCF.Data.Nat.Type
open import Interactive.LTC-PCF.Data.Nat.UnaryNumbers
open import Interactive.LTC-PCF.Data.Nat.UnaryNumbers.Totality

open import Interactive.LTC-PCF.Loop

open import Interactive.LTC-PCF.Program.Division.ConversionRules
open import Interactive.LTC-PCF.Program.Division.CorrectnessProof
open import Interactive.LTC-PCF.Program.Division.Division
open import Interactive.LTC-PCF.Program.Division.Result
open import Interactive.LTC-PCF.Program.Division.Specification
open import Interactive.LTC-PCF.Program.Division.Totality

open import Interactive.LTC-PCF.Program.GCD.Partial.CommonDivisor
open import Interactive.LTC-PCF.Program.GCD.Partial.ConversionRules
open import Interactive.LTC-PCF.Program.GCD.Partial.CorrectnessProof
open import Interactive.LTC-PCF.Program.GCD.Partial.Definitions
open import Interactive.LTC-PCF.Program.GCD.Partial.Divisible
open import Interactive.LTC-PCF.Program.GCD.Partial.GCD
open import Interactive.LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor
open import Interactive.LTC-PCF.Program.GCD.Partial.GreatestAnyCommonDivisor
open import Interactive.LTC-PCF.Program.GCD.Partial.Totality

open import Interactive.LTC-PCF.Program.GCD.Total.CommonDivisor
open import Interactive.LTC-PCF.Program.GCD.Total.CorrectnessProof
open import Interactive.LTC-PCF.Program.GCD.Total.ConversionRules
open import Interactive.LTC-PCF.Program.GCD.Total.Definitions
open import Interactive.LTC-PCF.Program.GCD.Total.Divisible
open import Interactive.LTC-PCF.Program.GCD.Total.GCD
open import Interactive.LTC-PCF.Program.GCD.Total.Totality
