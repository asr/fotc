------------------------------------------------------------------------------
-- All the Peano arithmetic modules
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.PA.Everything where

open import Combined.PA.Axiomatic.Mendelson.Base
open import Combined.PA.Axiomatic.Mendelson.Base.Consistency.Axioms
open import Combined.PA.Axiomatic.Mendelson.Properties
open import Combined.PA.Axiomatic.Mendelson.Relation.Binary.EqReasoning
open import Combined.PA.Axiomatic.Mendelson.Relation.Binary.PropositionalEquality

open import Combined.PA.Axiomatic.Standard.Base
open import Combined.PA.Axiomatic.Standard.Base.Consistency.Axioms
open import Combined.PA.Axiomatic.Standard.Properties

open import Combined.PA.Inductive.Base
open import Combined.PA.Inductive.Base.Core
open import Combined.PA.Inductive.Existential
open import Combined.PA.Inductive.Properties
open import Combined.PA.Inductive.PropertiesByInduction
open import Combined.PA.Inductive.Relation.Binary.EqReasoning
open import Combined.PA.Inductive.Relation.Binary.PropositionalEquality

open import Combined.PA.Inductive2Mendelson
open import Combined.PA.Inductive2Standard
