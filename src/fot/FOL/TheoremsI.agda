------------------------------------------------------------------------------
-- First-order logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.TheoremsI where

-- The theorems below are valid on intuitionistic logic and with an
-- empty domain.
open import FOL.Base hiding ( D≢∅ ; pem )

------------------------------------------------------------------------------
-- We postulate some formulae and propositional functions.
postulate
  A     : Set
  A¹ B¹ : D → Set
  A²    : D → D → Set

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

∀-intro : ((x : D) → A¹ x) → ∀ x → A¹ x
∀-intro h = h

∀-intro' : ((x : D) → A¹ x) → ⋀ A¹
∀-intro' = dfun

∀-elim : (t : D) → (∀ x → A¹ x) → A¹ t
∀-elim t h = h t

∀-elim' : (t : D) → ⋀ A¹ → A¹ t
∀-elim' = dapp

∃-intro : (t : D) → A¹ t → ∃ A¹
∃-intro t A¹x = t , A¹x

∃-elim : ∃ A¹ → ((x : D) → A¹ x → A) → A
∃-elim (x , A¹x) h = h x A¹x

-- Generalization of De Morgan's laws.
gDM₂ : ¬ (∃ A¹) ↔ (∀ {x} → ¬ (A¹ x))
gDM₂ = l→r , r→l
  where
  l→r : ¬ (∃ A¹) → ∀ {x} → ¬ (A¹ x)
  l→r h A¹x = h (_ , A¹x)

  r→l : (∀ {x} → ¬ (A¹ x)) → ¬ (∃ A¹)
  r→l h (x , A¹x) = h A¹x

gDM₂' : ¬ (∃ A¹) ⇔ (⋀[ x ] ¬ (A¹ x))
gDM₂' = fun l→r , fun r→l
  where
  l→r : ¬ (∃ A¹) → ⋀[ x ] ¬ A¹ x
  l→r h = dfun (λ d A¹d → h (d , A¹d))

  r→l : ⋀[ x ] ¬ A¹ x → ¬ ∃ A¹
  r→l (dfun f) (x , A¹x) = f x A¹x

-- Quantification over a variable that does not occur can be erased or
-- added.
∃-erase-add : (∃[ x ] A ∧ A¹ x) ↔ A ∧ (∃[ x ] A¹ x)
∃-erase-add = l→r , r→l
  where
  l→r : ∃[ x ] A ∧ A¹ x → A ∧ (∃[ x ] A¹ x)
  l→r (x , a , A¹x) = a , x , A¹x

  r→l : A ∧ (∃[ x ] A¹ x) → ∃[ x ] A ∧ A¹ x
  r→l (a , x , A¹x) = x , a , A¹x

-- Interchange of quantifiers.
-- The related theorem ∀x∃y.Axy → ∃y∀x.Axy is not (classically) valid.
∃∀ : ∃[ x ] (∀ y → A² x y) → ∀ y → ∃[ x ] A² x y
∃∀ (x , h) y = x , h y

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

-- Distribution of ∃ and ∨.
∃∨ : ∃[ x ](A¹ x ∨ B¹ x) → (∃[ x ] A¹ x) ∨ (∃[ x ] B¹ x)
∃∨ (x , inj₁ A¹x) = inj₁ (x , A¹x)
∃∨ (x , inj₂ B¹x) = inj₂ (x , B¹x)
