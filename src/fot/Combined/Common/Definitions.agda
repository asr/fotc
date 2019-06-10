------------------------------------------------------------------------------
-- Common definitions
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.Common.Definitions where

open import Common.FOL.FOL using ( ¬_ ; D )
open import Common.FOL.Relation.Binary.PropositionalEquality using ( _≡_ )

infix 4 _≢_

------------------------------------------------------------------------------
-- Inequality.
_≢_ : D → D → Set
x ≢ y = ¬ x ≡ y
{-# ATP definition _≢_ #-}
