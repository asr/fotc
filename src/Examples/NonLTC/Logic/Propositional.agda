------------------------------------------------------------------------------
-- Propositional logic examples
------------------------------------------------------------------------------

module Examples.NonLTC.Logic.Propositional where

open import Examples.NonLTC.Logic.Constants

------------------------------------------------------------------------------

-- We postulate some propositional variables (which are translated as
-- 0-ary predicates).
postulate
  P Q R : Set

-- Boolean laws.

∧∨-dist : P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
∧∨-dist = l→r , r→l
  where
    l→r : P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R
    l→r (p , inj₁ q) = inj₁ (p , q)
    l→r (p , inj₂ r) = inj₂ (p , r)

    r→l : P ∧ Q ∨ P ∧ R → P ∧ (Q ∨ R)
    r→l (inj₁ (p , q)) = p , inj₁ q
    r→l (inj₂ (p , r)) = p , inj₂ r
