------------------------------------------------------------------------------
-- Testing the eta-expansion
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module Eta1 where

postulate
  D   : Set
  A   : D → Set
  ∃   : (A : D → Set) → Set
  _≡_ : D → D → Set

-- Due to eta-contraction the Agda internal representation of test₁
-- and test₂, and test₃ and test₄ are the same. We eta-expand the
-- internal types before the translation to FOL.

postulate
  test₁ : ∀ d → A d → ∃ (λ e → A e)
  test₂ : ∀ d → A d → ∃ A

  test₃ : ∀ d → ∃ (λ e → d ≡ e)
  test₄ : ∀ d → ∃ (_≡_ d)

{-# ATP prove test₁ #-}
{-# ATP prove test₂ #-}
{-# ATP prove test₃ #-}
{-# ATP prove test₄ #-}
