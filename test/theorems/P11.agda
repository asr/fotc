------------------------------------------------------------------------------
-- Testing the translation of 11-ary predicates symbols
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module P11 where

postulate
  D : Set
  P : D → D → D → D → D → D → D → D → D → D → D → Set

postulate
  P-refl : ∀ {x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁} →
           P x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ →
           P x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁
{-# ATP prove P-refl #-}
