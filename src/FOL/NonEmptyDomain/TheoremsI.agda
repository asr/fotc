------------------------------------------------------------------------------
-- Theorems which require a non-empty domain
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOL.NonEmptyDomain.TheoremsI where

open import FOL.Base

-- References:
-- Elliott Mendelson. Introduction to mathematical logic. Chapman &
-- Hall, 4th edition, 1997.

------------------------------------------------------------------------------
-- We postulate some formulae and propositional functions.
postulate
  P⁰ : Set
  P¹ : D → Set

-- TODO: 2012-02-28. Fix the existential introduction rule.
-- ∃-intro : ((t : D) → P¹ t) → ∃ P¹
-- ∃-intro h = D≠∅ ,, h D≠∅

-- Let A be a formula. If x is not free in A then ⊢ (∃x)A ↔ A
-- (Mendelson, 1997, proposition 2.18 (b), p. 70).
∃-erase-add₁ : ∃ (λ _ → P⁰) ↔ P⁰
∃-erase-add₁ = l→r , r→l
  where
  l→r : ∃ (λ _ → P⁰) → P⁰
  l→r h = ∃-elim h (λ prf → prf)

  -- 2012-02-28. We required the existential witness.
  r→l : P⁰ → ∃ (λ _ → P⁰)
  r→l p⁰ = ∃-intro {x = D≠∅} p⁰

-- Quantification over a variable that does not occur can be erased or
-- added.
∃-erase-add₂ : (∃[ x ] P⁰ ∨ P¹ x) ↔ P⁰ ∨ (∃[ x ] P¹ x)
∃-erase-add₂ = l→r , r→l
  where
  l→r : ∃[ x ] (P⁰ ∨ P¹ x) → P⁰ ∨ (∃[ x ] P¹ x)
  l→r h = ∃-elim h (λ prf → [ (λ p⁰ → inj₁ p⁰) , (λ p¹ → inj₂ (∃-intro p¹)) ] prf)

  -- 2012-02-28. We required the existential witness.
  r→l : P⁰ ∨ (∃[ x ] P¹ x) → ∃[ x ] P⁰ ∨ P¹ x
  r→l (inj₁ p⁰) = ∃-intro {x = D≠∅} (inj₁ p⁰)
  r→l (inj₂ h)  = ∃-elim h (λ p¹ → ∃-intro (inj₂ p¹))
