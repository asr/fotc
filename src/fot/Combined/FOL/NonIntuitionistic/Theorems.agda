------------------------------------------------------------------------------
-- Non-intuitionistic logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Combined.FOL.NonIntuitionistic.Theorems where

open import Combined.FOL.Base hiding ( pem )

------------------------------------------------------------------------------
-- The principle of the excluded middle.
postulate pem : ∀ {A} → A ∨ ¬ A
{-# ATP prove pem #-}

-- The principle of indirect proof (proof by contradiction).
postulate ¬-elim : ∀ {A} → (¬ A → ⊥) → A
{-# ATP prove ¬-elim #-}

-- Double negation elimination.
postulate ¬¬-elim : ∀ {A} → ¬ ¬ A → A
{-# ATP prove ¬¬-elim #-}

-- The reductio ab absurdum rule. (Some authors uses this name for the
-- principle of indirect proof).
postulate raa : ∀ {A} → (¬ A → A) → A
{-# ATP prove raa #-}

-- ∃ in terms of ∀ and ¬.
postulate ¬∃¬→∀ : {A : D → Set} → ¬ (∃[ x ] ¬ A x) → ∀ {x} → A x
{-# ATP prove ¬∃¬→∀ #-}
