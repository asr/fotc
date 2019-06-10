------------------------------------------------------------------------------
-- First-order Peano arithmetic
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.PA.Inductive.README where

-- Formalization of first-order Peano arithmetic using Agda data types
-- and primitive recursive functions for addition and multiplication.

------------------------------------------------------------------------------
-- Inductive definitions
open import Combined.PA.Inductive.Base

-- Some properties
open import Combined.PA.Inductive.Properties

open import Combined.PA.Inductive.PropertiesByInduction
