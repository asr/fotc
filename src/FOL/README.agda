------------------------------------------------------------------------------
-- First-order logic (FOL)
------------------------------------------------------------------------------

module FOL.README where

-- Formalization of FOL using Agda's inductive notions.

------------------------------------------------------------------------------
-- Definition of the connectives and quantifiers
open import FOL.Base

-- Propositional logic theorems
open import FOL.Propositional.TheoremsATP
open import FOL.Propositional.TheoremsI

-- FOL theorems
open import FOL.TheoremsATP
open import FOL.TheoremsI

-- Logical schemata
open import FOL.SchemataATP

-- Non-empty domains
open import FOL.NonEmptyDomain.TheoremsATP
open import FOL.NonEmptyDomain.TheoremsI

-- Classical predicate logic theorems
open import FOL.ClassicalATP
open import FOL.ClassicalI
