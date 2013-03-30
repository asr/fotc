------------------------------------------------------------------------------
-- Non-intuitionistic logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --schematic-propositional-functions #-}
{-# OPTIONS --schematic-propositional-symbols #-}
{-# OPTIONS --without-K #-}

module FOL.NonIntuitionistic.TheoremsATP where

open import FOL.Base hiding ( pem )

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
