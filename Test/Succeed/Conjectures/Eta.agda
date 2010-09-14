------------------------------------------------------------------------------
-- Testing the eta-expansion
------------------------------------------------------------------------------

module Test.Succeed.Conjectures.Eta where

postulate
  D   : Set
  P   : D → Set
  ∃D  : (P : D → Set) → Set
  _≡_ : D → D → Set

-- Due to eta-contraction the Agda internal representation of test₁
-- and test₂, and test₃ and test₄ are the same. We eta-expand the
-- internal types before the translation to FOL.

postulate
  test₁ : (d : D) → P d → ∃D (λ e → P e)
  test₂ : (d : D) → P d → ∃D P

  test₃ : (d : D) → ∃D (λ e → d ≡ e)
  test₄ : (d : D) → ∃D (_≡_ d)

{-# ATP prove test₁ #-}
{-# ATP prove test₂ #-}
{-# ATP prove test₃ #-}
{-# ATP prove test₄ #-}
