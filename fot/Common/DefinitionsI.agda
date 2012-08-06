------------------------------------------------------------------------------
-- Common definitions
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Common.DefinitionsI where

open import Common.FOL.FOL using ( ¬_ ; D )
open import Common.FOL.Relation.Binary.PropositionalEquality using ( _≡_ )

-- We add 3 to the fixities of the standard library.
infix 7 _≢_

------------------------------------------------------------------------------
-- Inequality.
_≢_ : D → D → Set
x ≢ y = ¬ x ≡ y
