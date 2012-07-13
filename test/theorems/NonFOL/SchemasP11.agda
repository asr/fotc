------------------------------------------------------------------------------
-- Testing the translation of schemas with 11-ary predicates symbols
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- Requires option --non-fol-propositional-function@.

module NonFOL.SchemasP11 where

postulate
  D      : Set
  P-refl : {P : D → D → D → D → D → D → D → D → D → D → D → Set} →
           ∀ {x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁} →
           P x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ →
           P x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁
{-# ATP prove P-refl #-}
