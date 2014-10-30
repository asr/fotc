------------------------------------------------------------------------------
-- First-order Peano arithmetic
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module PA.Inductive.README where

-- Formalization of first-order Peano arithmetic using Agda data types
-- and primitive recursive functions for addition and multiplication.

------------------------------------------------------------------------------
-- Inductive definitions
open import PA.Inductive.Base

-- Some properties
open import PA.Inductive.PropertiesATP
open import PA.Inductive.PropertiesI

open import PA.Inductive.PropertiesByInduction
open import PA.Inductive.PropertiesByInductionATP
open import PA.Inductive.PropertiesByInductionI
