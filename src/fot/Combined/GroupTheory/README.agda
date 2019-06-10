------------------------------------------------------------------------------
-- Group theory
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.GroupTheory.README where

------------------------------------------------------------------------------
-- Description

-- Theory of groups using Agda postulates for the group axioms.

------------------------------------------------------------------------------
-- The axioms
open import Combined.GroupTheory.Base

-- Basic properties
open import Combined.GroupTheory.Properties

-- Commutator properties
open import Combined.GroupTheory.Commutator.Properties

-- Abelian groups
open import Combined.GroupTheory.AbelianGroup.Properties
