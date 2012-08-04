------------------------------------------------------------------------------
-- First-order Peano arithmetic
------------------------------------------------------------------------------

module PA.Inductive.README where

-- Formalization of first-order Peano aritmetic using Agda data types
-- and primitive recursive functions for addition and multiplication.

------------------------------------------------------------------------------
-- Inductive definitions
open import PA.Inductive.Base

-- Some properties
open import PA.Inductive.Properties
open import PA.Inductive.PropertiesATP
open import PA.Inductive.PropertiesI

open import PA.Inductive.PropertiesByInduction
open import PA.Inductive.PropertiesByInductionATP
open import PA.Inductive.PropertiesByInductionI
