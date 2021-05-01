------------------------------------------------------------------------------
-- Theorems which require a non-empty domain
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOL.NonEmptyDomain.Theorems where

-- The theorems below are valid on intuitionistic logic.
open import Interactive.FOL.Base hiding ( pem )

------------------------------------------------------------------------------
-- Variables

variable
  A  : Set
  A¹ : D → Set

------------------------------------------------------------------------------

∀→∃ : (∀ {x} → A¹ x) → ∃ A¹
∀→∃ h = D≢∅ , h

-- Let A be a formula. If x is not free in A then ⊢ (∃x)A ↔ A [van
-- Dalen, 2013, Theorem 3.5.2.iv, p 69].
∃-erase-add₁ : (∃[ _ ] A) ↔ A
∃-erase-add₁ = l→r , r→l
  where
  l→r : (∃[ _ ] A) → A
  l→r (_ , a) = a

  r→l : A → (∃[ _ ] A)
  r→l A = D≢∅ , A

-- Quantification over a variable that does not occur can be erased or
-- added.
∀-erase-add : ((x : D) → A) ↔ A
∀-erase-add = l→r , r→l
  where
  l→r : ((x : D) → A) → A
  l→r h = h D≢∅

  r→l : A → (x : D) → A
  r→l a _ = a

∃-erase-add₂ : (∃[ x ] (A ∨ A¹ x)) ↔ A ∨ (∃[ x ] A¹ x)
∃-erase-add₂ = l→r , r→l
  where
  l→r : ∃[ x ] (A ∨ A¹ x) → A ∨ (∃[ x ] A¹ x)
  l→r (x , inj₁ a)   = inj₁ a
  l→r (x , inj₂ A¹x) = inj₂ (x , A¹x)

  r→l : A ∨ (∃[ x ] A¹ x) → ∃[ x ] (A ∨ A¹ x)
  r→l (inj₁ a)         = D≢∅ , inj₁ a
  r→l (inj₂ (x , A¹x)) = x , inj₂ A¹x

------------------------------------------------------------------------------
-- References
--
-- van Dalen, Dirk (2013). Logic and Structure. 5th ed. Springer.
