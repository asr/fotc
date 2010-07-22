------------------------------------------------------------------------------
-- Propositional logic examples (without use LTC)
------------------------------------------------------------------------------

-- TODO

module Examples.Logic.Propositional where

open import Examples.Logic.Constants

------------------------------------------------------------------------------
-- We postulate some propositional variables (which are translated as
-- nullary predicate symbols).
postulate
  P Q R : Set

-- The introduction and elimination rules for the (classical)
-- propositional connectives.
postulate
  →I  : (P → Q) → P → Q -- TODO
  →E  : (P → Q) → P → Q -- TODO
  ∧I  : P ∧ Q → P ∧ Q   -- TODO
  ∧E₁ : P ∧ Q → P
  ∧E₂ : P ∧ Q → Q
  ∨I₁ : P → P ∨ Q
  ∨I₂ : Q → P ∨ Q
  ∨E  : (P → R) → (Q → R) → P ∨ Q → R
  ⊥E  : ⊥ → P
  ¬E : (¬ P → ⊥ ) → P  -- TODO
{-# ATP prove →I #-}
{-# ATP prove →E #-}
{-# ATP prove ∧I #-}
{-# ATP prove ∧E₁ #-}
{-# ATP prove ∧E₂ #-}
{-# ATP prove ∨I₁ #-}
{-# ATP prove ∨I₂ #-}
{-# ATP prove ∨E #-}
{-# ATP prove ⊥E #-}
{-# ATP prove ¬E #-}

-- Boolean laws

postulate
  ∧-ident : P ∧ ⊤       ↔ P
  ∨-ident : P ∨ ⊥       ↔ P
  ∧-dom   : P ∧ ⊥       ↔ ⊥
  ∨-dom   : P ∨ ⊤       ↔ ⊤
  ∧-idemp : P ∧ P       ↔ P
  ∨-idemp : P ∨ P       ↔ P
  dn      : ¬ ¬ P       ↔ P
  ∧-comm  : P ∧ Q       ↔ Q ∧ P
  ∨-comm  : P ∨ Q       ↔ Q ∨ P
  ∧-assoc : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R)
  ∨-assoc : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R)
  ∧-dist  : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)
  ∨-dist  : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R)
  DM₁     : ¬ (P ∧ Q)   ↔ ¬ P ∨ ¬ Q
  DM₂     : ¬ (P ∨ Q)   ↔ ¬ P ∧ ¬ Q
  abs₁    : P ∨ (P ∧ Q) ↔ P
  abs₂    : P ∧ (P ∨ Q) ↔ P
  ∧-neg   : P ∧ ¬ P     ↔ ⊥
  ∨-neg   : P ∨ ¬ P     ↔ ⊤

{-# ATP prove ∧-ident #-}
{-# ATP prove ∨-ident #-}
{-# ATP prove ∧-dom #-}
{-# ATP prove ∨-dom #-}
{-# ATP prove ∧-idemp #-}
{-# ATP prove ∨-idemp #-}
{-# ATP prove dn #-}
{-# ATP prove ∧-comm #-}
{-# ATP prove ∨-comm #-}
{-# ATP prove ∧-assoc #-}
{-# ATP prove ∨-assoc #-}
{-# ATP prove ∧-dist #-}
{-# ATP prove ∨-dist #-}
{-# ATP prove DM₁ #-}
{-# ATP prove DM₂ #-}
{-# ATP prove abs₁ #-}
{-# ATP prove abs₂ #-}
{-# ATP prove ∧-neg #-}
{-# ATP prove ∨-neg #-}
