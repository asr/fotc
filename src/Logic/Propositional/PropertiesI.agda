------------------------------------------------------------------------------
-- Propositional logic examples
------------------------------------------------------------------------------

module Logic.Propositional.PropertiesI where

open import Logic.Constants

------------------------------------------------------------------------------
-- Boolean laws.

∧∨-dist : {P Q R : Set} → P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
∧∨-dist {P} {Q} {R} = l→r , r→l
  where
    l→r : P ∧ (Q ∨ R) → P ∧ Q ∨ P ∧ R
    l→r (p , inj₁ q) = inj₁ (p , q)
    l→r (p , inj₂ r) = inj₂ (p , r)

    r→l : P ∧ Q ∨ P ∧ R → P ∧ (Q ∨ R)
    r→l (inj₁ (p , q)) = p , inj₁ q
    r→l (inj₂ (p , r)) = p , inj₂ r
