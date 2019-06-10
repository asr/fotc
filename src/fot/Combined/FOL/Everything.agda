------------------------------------------------------------------------------
-- All the predicate logic modules
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOL.Everything where

open import Combined.FOL.Base
open import Combined.FOL.ExclusiveDisjunction.Base
open import Combined.FOL.ExclusiveDisjunction.Theorems
open import Combined.FOL.NonEmptyDomain.Theorems
open import Combined.FOL.NonIntuitionistic.Theorems
open import Combined.FOL.PropositionalLogic.Theorems
open import Combined.FOL.Schemata
open import Combined.FOL.Theorems
