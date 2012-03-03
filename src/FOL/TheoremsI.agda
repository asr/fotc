------------------------------------------------------------------------------
-- FOL theorems
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOL.TheoremsI where

open import FOL.Base

------------------------------------------------------------------------------
-- We postulate some formulae and propositional functions.
postulate
  A  : Set
  A¹ : D → Set
  A² : D → D → Set

-- The introduction and elimination rules for the quantifiers are theorems.
{-
      φ(x)
  -----------  ∀-intro
    ∀x.φ(x)

    ∀x.φ(x)
  -----------  ∀-elim
     φ(t)

      φ(t)
  -----------  ∃-intro
    ∃x.φ(x)

   ∃x.φ(x)   φ(x) → ψ
 ----------------------  ∃-elim
           ψ
-}

-- It is necessary postulate a non-empty domain. See
-- FOL.NonEmptyDomain.TheoremsI/ATP.∃I.
--
-- ∃-intro : ((t : D) → A¹ t) → ∃ A¹

∃-elim' : ∃ A¹ → ({x : D} → A¹ x → A) → A
∃-elim' = ∃-elim

-- Generalization of De Morgan's laws.
gDM₂ : ¬ (∃ A¹) ↔ (∀ {x} → ¬ (A¹ x))
gDM₂ = l→r , r→l
  where
  l→r : ¬ (∃ A¹) → ∀ {x} → ¬ (A¹ x)
  l→r h A¹x = h (_ , A¹x)

  r→l : (∀ {x} → ¬ (A¹ x)) → ¬ (∃ A¹)
  r→l h₁ h₂ = ∃-elim h₂ h₁

-- Quantification over a variable that does not occur can be erased or
-- added.
∃-erase-add : (∃[ x ] A ∧ A¹ x) ↔ A ∧ (∃[ x ] A¹ x)
∃-erase-add = l→r , r→l
  where
  l→r : ∃[ x ] A ∧ A¹ x → A ∧ (∃[ x ] A¹ x)
  l→r h = ∃-elim h (λ prf → (∧-proj₁ prf) , _ , ∧-proj₂ prf)

  r→l : A ∧ (∃[ x ] A¹ x) → ∃[ x ] A ∧ A¹ x
  r→l (a , h) = ∃-elim h (λ prf → _ , a , prf)

-- Interchange of quantifiers.
-- The related theorem ∀x∃y.Axy → ∃y∀x.Axy is not (classically) valid.
∃∀ : ∃[ x ] (∀ y → A² x y) → ∀ y → ∃[ x ] A² x y
∃∀ h y = ∃-elim h (λ prf → _ , prf y)

-- ∃ in terms of ∀ and ¬.
∃→¬∀¬ : ∃[ x ] A¹ x → ¬ (∀ {x} → ¬ A¹ x)
∃→¬∀¬ (_ , A¹x) h = h A¹x

∃¬→¬∀ : ∃[ x ] ¬ A¹ x → ¬ (∀ {x} → A¹ x)
∃¬→¬∀ (_ , h₁) h₂ = h₁ h₂

-- ∀ in terms of ∃ and ¬.
∀→¬∃¬ : (∀ {x} → A¹ x) → ¬ (∃[ x ] ¬ A¹ x)
∀→¬∃¬ h₁ (_ ,  h₂) = h₂ h₁

∀¬→¬∃ : (∀ {x} → ¬ A¹ x) → ¬ (∃[ x ] A¹ x)
∀¬→¬∃ h₁ (_ , h₂) = h₁ h₂
