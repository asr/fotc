------------------------------------------------------------------------------
-- All the Peano arithmetic modules
------------------------------------------------------------------------------

module PA.Everything where

open import PA.Axiomatic.Mendelson.Base
open import PA.Axiomatic.Mendelson.Base.ConsistencyTest
open import PA.Axiomatic.Mendelson.PropertiesATP
open import PA.Axiomatic.Mendelson.PropertiesI
open import PA.Axiomatic.Mendelson.Relation.Binary.EqReasoning
open import PA.Axiomatic.Mendelson.Relation.Binary.PropositionalEqualityI
open import PA.Axiomatic.Mendelson.Relation.Binary.PropositionalEqualityATP

open import PA.Axiomatic.Standard.Base
open import PA.Axiomatic.Standard.Base.ConsistencyTest
open import PA.Axiomatic.Standard.PropertiesATP
open import PA.Axiomatic.Standard.PropertiesI
open import PA.Axiomatic.Standard.Relation.Binary.EqReasoning

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

open import PA.Inductive2Mendelson
open import PA.Inductive2Standard
