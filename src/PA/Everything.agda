------------------------------------------------------------------------------
-- All the Peano arithmetic modules
------------------------------------------------------------------------------

module PA.Everything where

open import PA.Axiomatic.Base
open import PA.Axiomatic.Base.ConsistencyTest
open import PA.Axiomatic.PropertiesATP
open import PA.Axiomatic.PropertiesI
open import PA.Axiomatic.Relation.Binary.EqReasoning
open import PA.Axiomatic.Relation.Binary.PropositionalEqualityI
open import PA.Axiomatic.Relation.Binary.PropositionalEqualityATP

open import PA.Inductive.Base
open import PA.Inductive.Base.Core
open import PA.Inductive.Properties
open import PA.Inductive.PropertiesATP
open import PA.Inductive.PropertiesI
open import PA.Inductive.PropertiesByInduction
open import PA.Inductive.PropertiesByInductionATP
open import PA.Inductive.PropertiesByInductionI
open import PA.Inductive.Relation.Binary.EqReasoning
open import PA.Inductive.Relation.Binary.PropositionalEquality

open import PA.Inductive2Axiomatic
