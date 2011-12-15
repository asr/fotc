------------------------------------------------------------------------------
-- All the distributive laws modules
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DistributiveLaws.Everything where

open import DistributiveLaws.Base
open import DistributiveLaws.Base.ConsistencyTest

open import DistributiveLaws.Relation.Binary.EqReasoning

open import DistributiveLaws.TaskB-I

open import DistributiveLaws.TaskB-ATP
open import DistributiveLaws.TaskB-AllStepsATP
open import DistributiveLaws.TaskB-HalvedStepsATP
open import DistributiveLaws.TaskB-TopDownATP
