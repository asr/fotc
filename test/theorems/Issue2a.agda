------------------------------------------------------------------------------
-- Issue in the translation of definitions using λ-terms.
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Issue2a where

postulate
  D   : Set
  _≡_ : D → D → Set

-- The translations of foo₁ and foo₂ should be the same.
foo₁ : D → D
foo₁ d = d
{-# ATP definition foo₁ #-}

foo₂ : D → D
foo₂ = λ d → d
{-# ATP definition foo₂ #-}

postulate bar₁ : ∀ d → d ≡ foo₁ d
{-# ATP prove bar₁ #-}

postulate bar₂ : ∀ d → d ≡ foo₂ d
{-# ATP prove bar₂ #-}
