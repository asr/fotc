------------------------------------------------------------------------------
-- Propositional logic theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- This module contains some examples showing the use of the ATPs to
-- prove theorems from propositional logic.

module FOL.Propositional.TheoremsATP where

open import FOL.Base

------------------------------------------------------------------------------
-- We postulate some propositional formulae (which are translated as
-- 0-ary predicates).
postulate P Q R : Set

------------------------------------------------------------------------------
-- The introduction and elimination rules for the intuitionist
-- propositional connectives are theorems.

postulate
  →I  : (P → Q) → P → Q
  →E  : (P → Q) → P → Q
  →I' : (P → Q) → P → Q
  →E' : (P ⇒ Q) ⇒ P ⇒ Q
{-# ATP prove →I #-}
{-# ATP prove →E #-}
{-# ATP prove →I' #-}
{-# ATP prove →E' #-}

postulate
  ∧I   : P → Q → P ∧ Q
  ∧E₁  : P ∧ Q → P
  ∧E₂  : P ∧ Q → Q
  ∧I'  : P ⇒ Q ⇒ P ∧ Q
  ∧E₂' : P ∧ Q ⇒ Q
  ∧E₁' : P ∧ Q ⇒ P
{-# ATP prove ∧I #-}
{-# ATP prove ∧E₁ #-}
{-# ATP prove ∧E₂ #-}
{-# ATP prove ∧I' #-}
{-# ATP prove ∧E₁' #-}
{-# ATP prove ∧E₂' #-}

postulate
  ∨I₁  : P → P ∨ Q
  ∨I₂  : Q → P ∨ Q
  ∨E   : (P → R) → (Q → R) → P ∨ Q → R
  ∨I₁' : P ⇒ P ∨ Q
  ∨I₂' : Q ⇒ P ∨ Q
  ∨E'  : (P ⇒ R) ⇒ (Q ⇒ R) ⇒ P ∨ Q ⇒ R
{-# ATP prove ∨I₁ #-}
{-# ATP prove ∨I₂ #-}
{-# ATP prove ∨E #-}
{-# ATP prove ∨I₁' #-}
{-# ATP prove ∨I₂' #-}
{-# ATP prove ∨E' #-}

postulate
  ⊥E  : ⊥ → P
  ⊥E' : ⊥ ⇒ P
{-# ATP prove ⊥E #-}
{-# ATP prove ⊥E' #-}

------------------------------------------------------------------------------
-- Boolean laws (there are some non-intuitionistic laws)

postulate
  ∧-ident : P ∧ ⊤       ↔ P
  ∨-ident : P ∨ ⊥       ↔ P
  ∧-dom   : P ∧ ⊥       ↔ ⊥
  ∨-dom   : P ∨ ⊤       ↔ ⊤
  ∧-idemp : P ∧ P       ↔ P
  ∨-idemp : P ∨ P       ↔ P
  dn      : ¬ ¬ P       ↔ P
  ∧-comm  : P ∧ Q       → Q ∧ P
  ∨-comm  : P ∨ Q       → Q ∨ P
  ∧-assoc : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R
  ∨-assoc : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R
  ∧∨-dist : P ∧ (Q ∨ R) ↔ P ∧ Q ∨ P ∧ R
  ∨∧-dist : P ∨ Q ∧ R   ↔ (P ∨ Q) ∧ (P ∨ R)
  DM₁     : ¬ (P ∨ Q)   ↔ ¬ P ∧ ¬ Q
  DM₂     : ¬ (P ∧ Q)   ↔ ¬ P ∨ ¬ Q
  abs₁    : P ∨ P ∧ Q   ↔ P
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
{-# ATP prove ∧∨-dist #-}
{-# ATP prove ∨∧-dist #-}
{-# ATP prove DM₁ #-}
{-# ATP prove DM₂ #-}
{-# ATP prove abs₁ #-}
{-# ATP prove abs₂ #-}
{-# ATP prove ∧-neg #-}
{-# ATP prove ∨-neg #-}

------------------------------------------------------------------------------
-- Theorems related with the definition of logical connectives in
-- terms of others

postulate
  ↔-def  : (P ↔ Q) ↔ (P → Q) ∧ (Q → P)
  →-def  : P → Q   ↔ ¬ P ∨ Q
  ∨₁-def : P ∨ Q   ↔ ¬ P → Q
  ∨₂-def : P ∨ Q   ↔ ¬ (¬ P ∧ ¬ Q)
  ∧-def  : P ∧ Q   ↔ ¬ (¬ P ∨ ¬ Q)
  ¬-def  : ¬ P     ↔ P → ⊥
  ⊥-def  : ⊥       ↔ P ∧ ¬ P
  ⊤-def  : ⊤       ↔ ¬ ⊥
{-# ATP prove ↔-def #-}
{-# ATP prove →-def #-}
{-# ATP prove ∨₁-def #-}
{-# ATP prove ∨₂-def #-}
{-# ATP prove ∧-def #-}
{-# ATP prove ¬-def #-}
{-# ATP prove ⊥-def #-}
{-# ATP prove ⊤-def #-}

------------------------------------------------------------------------------
-- Some intuitionistic theorems

postulate →-transposition : (P → Q) → ¬ Q → ¬ P
{-# ATP prove →-transposition #-}

postulate
  i₁ : P → Q → P
  i₂ : (P → Q → R) → (P → Q) → P → R
  i₃ : P → ¬ ¬ P
  i₄ : ¬ ¬ ¬ P → ¬ P
  i₅ : ((P ∧ Q) → R) ↔ (P → (Q → R))
  i₆ : ¬ ¬ (P ∨ ¬ P)
  i₇ : (P ∨ ¬ P) → ¬ ¬ P → P
{-# ATP prove i₁ #-}
{-# ATP prove i₂ #-}
{-# ATP prove i₃ #-}
{-# ATP prove i₄ #-}
{-# ATP prove i₅ #-}
{-# ATP prove i₆ #-}
{-# ATP prove i₇ #-}

------------------------------------------------------------------------------
-- Some non-intuitionistic theorems

postulate ←-transposition : (¬ Q → ¬ P) → P → Q
{-# ATP prove ←-transposition #-}

postulate
  ni₁ : ((P → Q) → P) → P
  ni₂ : P ∨ ¬ P
  ni₃ : ¬ ¬ P → P
  ni₄ : (P → Q) → (¬ P → Q) → Q
  ni₅ : (P ∨ Q → P) ∨ (P ∨ Q → Q)
  ni₆ : (¬ ¬ P → P) → P ∨ ¬ P
{-# ATP prove ni₁ #-}
{-# ATP prove ni₂ #-}
{-# ATP prove ni₃ #-}
{-# ATP prove ni₄ #-}
{-# ATP prove ni₅ #-}
{-# ATP prove ni₆ #-}
