------------------------------------------------------------------------------
-- First-order logic
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.README where

------------------------------------------------------------------------------
-- Description

-- Formalization of first-order logic using Agda's inductive notions.

------------------------------------------------------------------------------
-- Definition of the connectives and quantifiers
open import FOL.Base

-- Propositional logic theorems
open import FOL.Propositional.TheoremsATP
open import FOL.Propositional.TheoremsI

-- First-order logic theorems
open import FOL.TheoremsATP
open import FOL.TheoremsI

-- Logical schemata
open import FOL.SchemataATP

-- Non-empty domains
open import FOL.NonEmptyDomain.TheoremsATP
open import FOL.NonEmptyDomain.TheoremsI

-- Non-intuitionistic logic theorems
open import FOL.NonIntuitionistic.TheoremsATP
open import FOL.NonIntuitionistic.TheoremsI
