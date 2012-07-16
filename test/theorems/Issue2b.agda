------------------------------------------------------------------------------
-- Issue in the translation of definitions using λ-terms.
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Issue2b where

postulate
  D   : Set
  _≡_ : D → D → Set

-- The translations of foo₁ and foo₂ should be the same.
foo₁ : D → D → D
foo₁ d _ = d
{-# ATP definition foo₁ #-}

foo₂ : D → D → D
foo₂ = λ d _ → d
{-# ATP definition foo₂ #-}

postulate bar₁ : ∀ d e → d ≡ foo₁ d e
{-# ATP prove bar₁ #-}

postulate bar₂ : ∀ d e → d ≡ foo₂ d e
{-# ATP prove bar₂ #-}
