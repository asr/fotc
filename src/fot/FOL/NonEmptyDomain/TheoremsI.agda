------------------------------------------------------------------------------
-- Theorems which require a non-empty domain
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.NonEmptyDomain.TheoremsI where

-- The theorems below are valid on intuitionistic logic.
open import FOL.Base hiding ( pem )

------------------------------------------------------------------------------
-- We postulate some formulae and propositional functions.
postulate
  A  : Set
  A¹ : D → Set

∀→∃ : (∀ {x} → A¹ x) → ∃ A¹
∀→∃ h = D≢∅ , h

-- Let A be a formula. If x is not free in A then ⊢ (∃x)A ↔ A
-- (Mendelson 1997, proposition 2.18 (b), p. 70).
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
-- Mendelson, Elliott (1997). Introduction to Mathematical Logic. 4th
-- ed. Chapman & Hall.
