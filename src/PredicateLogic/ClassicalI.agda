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
postulate pem : ∀ {A} → A ∨ ¬ A
{-# ATP prove pem #-}

-- The principle of indirect proof (proof by contradiction).
¬E : ∀ {A} → (¬ A → ⊥) → A
¬E h = [ (λ a → a) , (λ ¬a → ⊥-elim (h ¬a)) ] pem

-- The reductio ab absurdum rule. (Some authors uses this name for the
-- principle of indirect proof).
raa : ∀ {A} → (¬ A → A) → A
raa h = [ (λ a → a) , h ] pem
