------------------------------------------------------------------------------
-- First-order logic
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOL.README where

------------------------------------------------------------------------------
-- Description

-- Formalization of first-order logic using Agda's inductive notions.

------------------------------------------------------------------------------
-- Definition of the connectives and quantifiers
open import Combined.FOL.Base

-- Propositional logic theorems
open import Combined.FOL.ExclusiveDisjunction.Theorems
open import Combined.FOL.PropositionalLogic.Theorems

-- First-order logic theorems
open import Combined.FOL.Theorems

-- Logical schemata
open import Combined.FOL.Schemata

-- Non-empty domains
open import Combined.FOL.NonEmptyDomain.Theorems

-- Non-intuitionistic logic theorems
open import Combined.FOL.NonIntuitionistic.Theorems
