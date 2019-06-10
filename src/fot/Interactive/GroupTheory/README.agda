------------------------------------------------------------------------------
-- Group theory
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.GroupTheory.README where

------------------------------------------------------------------------------
-- Description

-- Theory of groups using Agda postulates for the group axioms.

------------------------------------------------------------------------------
-- The axioms
open import Interactive.GroupTheory.Base

-- Basic properties
open import Interactive.GroupTheory.Properties

-- Commutator properties
open import Interactive.GroupTheory.Commutator.Properties

-- Abelian groups
open import Interactive.GroupTheory.AbelianGroup.Properties
