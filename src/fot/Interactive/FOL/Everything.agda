------------------------------------------------------------------------------
-- All the predicate logic modules
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOL.Everything where

open import Interactive.FOL.Base
open import Interactive.FOL.ExclusiveDisjunction.Base
open import Interactive.FOL.ExclusiveDisjunction.Theorems
open import Interactive.FOL.NonEmptyDomain.Theorems
open import Interactive.FOL.NonIntuitionistic.Theorems
open import Interactive.FOL.PropositionalLogic.Theorems
open import Interactive.FOL.Theorems
