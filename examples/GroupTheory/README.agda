------------------------------------------------------------------------------
-- Group theory
------------------------------------------------------------------------------

module GroupTheory.README where

-- Theory of groups using Agda postulates for the group axioms.

------------------------------------------------------------------------------
-- The axioms
open import GroupTheory.Base

-- Basic properties
open import GroupTheory.PropertiesATP
open import GroupTheory.PropertiesI

-- Commutator properties
open import GroupTheory.Commutator.PropertiesATP
open import GroupTheory.Commutator.PropertiesI

-- Abelian groups
open import GroupTheory.AbelianGroup.PropertiesATP
