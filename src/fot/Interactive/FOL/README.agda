------------------------------------------------------------------------------
-- First-order logic
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOL.README where

------------------------------------------------------------------------------
-- Description

-- Formalization of first-order logic using Agda's inductive notions.

------------------------------------------------------------------------------
-- Definition of the connectives and quantifiers
open import Interactive.FOL.Base

-- Propositional logic theorems
open import Interactive.FOL.ExclusiveDisjunction.Theorems
open import Interactive.FOL.PropositionalLogic.Theorems

-- First-order logic theorems
open import Interactive.FOL.Theorems

-- Non-empty domains
open import Interactive.FOL.NonEmptyDomain.Theorems

-- Non-intuitionistic logic theorems
open import Interactive.FOL.NonIntuitionistic.Theorems
