------------------------------------------------------------------------------
-- Classical logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The ATPs work in classical logic, therefore we also can prove some
-- classical logic theorems.

module PredicateLogic.ClassicalATP where

open import PredicateLogic.Constants

------------------------------------------------------------------------------

-- The principle of the excluded middle.
postulate pem : ∀ {P} → P ∨ ¬ P
{-# ATP prove pem #-}

-- The principle of indirect proof (proof by contradiction).
postulate ¬E : ∀ {P} → (¬ P → ⊥) → P
{-# ATP prove ¬E #-}

-- The reductio ab absurdum rule. (Some authors uses this name for the
-- principle of indirect proof).
postulate raa : ∀ {P} → (¬ P → P) → P
{-# ATP prove raa #-}
