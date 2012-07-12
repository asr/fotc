------------------------------------------------------------------------------
-- Testing the erasing of the duplicate definitions required by a conjecture
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module DuplicateAgdaDefinitions1 where

infix 7 _≈_

------------------------------------------------------------------------------

postulate
  D   : Set
  _≈_ : D → D → Set

Eq : D → D → Set
Eq x y = x ≈ y
{-# ATP definition Eq #-}

postulate Eq-trans : ∀ {x y z} → Eq x y → Eq y z → Eq x z

postulate Eq-trans₂ : ∀ {w x y z} → Eq w x → Eq x y → Eq y z → Eq w z
{-# ATP prove Eq-trans₂ Eq-trans #-}
