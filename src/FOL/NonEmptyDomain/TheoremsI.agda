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
  A  : Set
  A¹ : D → Set

-- TODO: 2012-02-28. Fix the existential introduction rule.
-- ∃-intro : ((t : D) → A¹ t) → ∃ A¹
-- ∃-intro h = D≠∅ ,, h D≠∅

∀→∃ : (∀ {x} → A¹ x) → ∃ A¹
∀→∃ h = ∃-intro {x = D≠∅} h

-- Let A be a formula. If x is not free in A then ⊢ (∃x)A ↔ A
-- (Mendelson, 1997, proposition 2.18 (b), p. 70).
∃-erase-add₁ : ∃ (λ _ → A) ↔ A
∃-erase-add₁ = l→r , r→l
  where
  l→r : ∃ (λ _ → A) → A
  l→r h = ∃-elim h (λ prf → prf)

  -- 2012-02-28. We required the existential witness.
  r→l : A → ∃ (λ _ → A)
  r→l A = ∃-intro {x = D≠∅} A

-- Quantification over a variable that does not occur can be erased or
-- added.
∃-erase-add₂ : (∃[ x ] A ∨ A¹ x) ↔ A ∨ (∃[ x ] A¹ x)
∃-erase-add₂ = l→r , r→l
  where
  l→r : ∃[ x ] (A ∨ A¹ x) → A ∨ (∃[ x ] A¹ x)
  l→r h = ∃-elim h (λ prf → [ (λ a → inj₁ a )
                            , (λ A¹x → inj₂ (∃-intro A¹x))
                            ] prf
                   )

  -- 2012-02-28. We required the existential witness.
  r→l : A ∨ (∃[ x ] A¹ x) → ∃[ x ] A ∨ A¹ x
  r→l (inj₁ a) = ∃-intro {x = D≠∅} (inj₁ a)
  r→l (inj₂ h) = ∃-elim h (λ A¹x → ∃-intro (inj₂ A¹x))
