------------------------------------------------------------------------------
-- Non-intuitionistic logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Interactive.FOL.NonIntuitionistic.Theorems where

-- The theorems below are valid with an empty domain.
open import Interactive.FOL.Base hiding ( D≢∅ )

------------------------------------------------------------------------------
-- Variables

variable
  A  : Set
  A¹ : D → Set

------------------------------------------------------------------------------
-- Reductio ab absurdum rule (proof by contradiction).
raa : (¬ A → ⊥) → A
raa h = case (λ a → a) (λ ¬a → ⊥-elim (h ¬a)) pem

-- ¬∃¬ in terms of ∀.
¬∃¬→∀ : ¬ (∃[ x ] ¬ A¹ x) → ∀ {x} → A¹ x
¬∃¬→∀ h {x} = raa (λ ah → h (x , ah))
