------------------------------------------------------------------------------
-- All the distributive laws modules
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.DistributiveLaws.Everything where

open import Combined.DistributiveLaws.Base
open import Combined.DistributiveLaws.Base.Consistency.Axioms

open import Combined.DistributiveLaws.Lemma3
open import Combined.DistributiveLaws.Lemma4
open import Combined.DistributiveLaws.Lemma5
open import Combined.DistributiveLaws.Lemma6

open import Combined.DistributiveLaws.TaskB-AllSteps
open import Combined.DistributiveLaws.TaskB-HalvedSteps
open import Combined.DistributiveLaws.TaskB-TopDown
open import Combined.DistributiveLaws.TaskB.Unproved
