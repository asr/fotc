------------------------------------------------------------------------------
-- Classical logic theorems
------------------------------------------------------------------------------

-- The ATPs work in classical logic, therefore we also can prove some
-- classical logic theorems.

module PredicateLogic.ClassicalATP where

open import PredicateLogic.Constants

------------------------------------------------------------------------------

-- We postulate some propositional variables (which are translated as
-- 0-ary predicates).
postulate
  P : Set

-- The reductio ab absurdum rule.
postulate ¬E : (¬ P → ⊥) → P
{-# ATP prove ¬E #-}

-- The law of the excluded middle.
postulate lem : P ∨ ¬ P
{-# ATP prove lem #-}
