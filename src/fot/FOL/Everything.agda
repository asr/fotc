------------------------------------------------------------------------------
-- All the predicate logic modules
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.Everything where

open import FOL.Base
open import FOL.ExclusiveDisjunction.Base
open import FOL.ExclusiveDisjunction.TheoremsATP
open import FOL.ExclusiveDisjunction.TheoremsI
open import FOL.NonEmptyDomain.TheoremsATP
open import FOL.NonEmptyDomain.TheoremsI
open import FOL.NonIntuitionistic.TheoremsATP
open import FOL.NonIntuitionistic.TheoremsI
open import FOL.PropositionalLogic.TheoremsATP
open import FOL.PropositionalLogic.TheoremsI
open import FOL.SchemataATP
open import FOL.TheoremsATP
open import FOL.TheoremsI
