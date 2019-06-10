------------------------------------------------------------------------------
-- All the Peano arithmetic modules
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.PA.Everything where

open import Interactive.PA.Axiomatic.Mendelson.Base
open import Interactive.PA.Axiomatic.Mendelson.Properties
open import Interactive.PA.Axiomatic.Mendelson.Relation.Binary.EqReasoning
open import Interactive.PA.Axiomatic.Mendelson.Relation.Binary.PropositionalEquality

open import Interactive.PA.Axiomatic.Standard.Base
open import Interactive.PA.Axiomatic.Standard.Properties

open import Interactive.PA.Inductive.Base
open import Interactive.PA.Inductive.Base.Core
open import Interactive.PA.Inductive.Existential
open import Interactive.PA.Inductive.Properties
open import Interactive.PA.Inductive.PropertiesByInduction
open import Interactive.PA.Inductive.Relation.Binary.EqReasoning
open import Interactive.PA.Inductive.Relation.Binary.PropositionalEquality

open import Interactive.PA.Inductive2Mendelson
open import Interactive.PA.Inductive2Standard
