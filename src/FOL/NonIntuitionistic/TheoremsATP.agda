------------------------------------------------------------------------------
-- Non-intuitionistic logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

module FOL.NonIntuitionistic.TheoremsATP where

-- The ATPs work in classical logic, therefore we also can prove some
-- non-intuitionistic logic theorems.

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
