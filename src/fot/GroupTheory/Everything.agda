------------------------------------------------------------------------------
-- All the group theory modules
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module GroupTheory.Everything where

open import GroupTheory.Base
open import GroupTheory.Base.Consistency.Axioms

open import GroupTheory.AbelianGroup.Base
open import GroupTheory.AbelianGroup.Base.Consistency.Axioms
open import GroupTheory.AbelianGroup.PropertiesATP

open import GroupTheory.Commutator
open import GroupTheory.Commutator.PropertiesATP
open import GroupTheory.Commutator.PropertiesI

open import GroupTheory.PropertiesATP
open import GroupTheory.PropertiesI
