------------------------------------------------------------------------------
-- Classical logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The ATPs work in classical logic, therefore we also can prove some
-- classical logic theorems.

module FOL.ClassicalATP where

open import FOL.Base

------------------------------------------------------------------------------

-- The principle of the excluded middle.
postulate pem : ∀ {A} → A ∨ ¬ A
{-# ATP prove pem #-}

-- The principle of indirect proof (proof by contradiction).
postulate ¬E : ∀ {A} → (¬ A → ⊥) → A
{-# ATP prove ¬E #-}

-- The reductio ab absurdum rule. (Some authors uses this name for the
-- principle of indirect proof).
postulate raa : ∀ {A} → (¬ A → A) → A
{-# ATP prove raa #-}
