------------------------------------------------------------------------------
-- Non-intuitionistic logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module FOL.NonIntuitionistic.TheoremsI where

-- The theorems below are valid with an empty domain.
open import FOL.Base hiding ( D≢∅ )

------------------------------------------------------------------------------
-- The principle of indirect proof (proof by contradiction).
¬-elim : ∀ {A} → (¬ A → ⊥) → A
¬-elim h = case (λ a → a) (λ ¬a → ⊥-elim (h ¬a)) pem

-- Double negation elimination.
¬¬-elim : ∀ {A} → ¬ ¬ A → A
¬¬-elim {A} h = ¬-elim h

-- The reductio ab absurdum rule. (Some authors uses this name for the
-- principle of indirect proof).
raa : ∀ {A} → (¬ A → A) → A
raa h = case (λ a → a) h pem

-- ∃ in terms of ∀ and ¬.
¬∃¬→∀ : {A : D → Set} → ¬ (∃[ x ] ¬ A x) → ∀ {x} → A x
¬∃¬→∀ h {x} = ¬-elim (λ ah → h (x , ah))
