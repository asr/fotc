------------------------------------------------------------------------------
-- Classical logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- The ATPs work in classical logic, therefore we add the principle of
-- the exclude middle for prove some classical logic theorems.

module PredicateLogic.ClassicalI where

open import PredicateLogic.Constants

------------------------------------------------------------------------------

-- The principle of the excluded middle.
postulate pem : ∀ {P} → P ∨ ¬ P
{-# ATP prove pem #-}

-- The principle of indirect proof (proof by contradiction).
¬E : ∀ {P} → (¬ P → ⊥) → P
¬E h = [ (λ p → p) , (λ ¬p → ⊥-elim (h ¬p)) ] pem

-- The reductio ab absurdum rule. (Some authors uses this name for the
-- principle of indirect proof).
raa : ∀ {P} → (¬ P → P) → P
raa h = [ (λ p → p) , h ] pem
