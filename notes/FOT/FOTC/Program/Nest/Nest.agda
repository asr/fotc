------------------------------------------------------------------------------
-- FOTC version of a nested recursive function by the
-- Bove-Capretta method
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. Vol. 2152 of LNCS. 2001

module FOT.FOTC.Program.Nest.Nest where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base

open import FOTC.Data.Nat

import FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI
open module WF = FOTC.Data.Nat.Induction.Acc.WellFoundedInductionI.WF-LT

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI

------------------------------------------------------------------------------

-- The nest function.
postulate
  nest   : D → D
  nest-0 :       nest zero      ≡ zero
  nest-S : ∀ d → nest (succ₁ d) ≡ nest (nest d)

data Dom : D → Set where
  dom0 :                              Dom zero
  domS : ∀ d → Dom d → Dom (nest d) → Dom (succ₁ d)

-- Inductive principle associated to the domain predicate.
indDom : (P : D → Set) →
         P zero →
         (∀ {d} → Dom d → P d → Dom (nest d) → P (nest d) → P (succ₁ d)) →
         ∀ {d} → Dom d → P d
indDom P P0 ih dom0           = P0
indDom P P0 ih (domS d h₁ h₂) = ih h₁ (indDom P P0 ih h₁) h₂ (indDom P P0 ih h₂)

-- The domain predicate is total.
dom-N : ∀ d → Dom d → N d
dom-N .zero      dom0           = zN
dom-N .(succ₁ d) (domS d h₁ h₂) = sN (dom-N d h₁)

nest-x≡0 : ∀ {n} → N n → nest n ≡ zero
nest-x≡0 zN      = nest-0
nest-x≡0 (sN {n} Nn) =
  nest (succ₁ n) ≡⟨ nest-S n ⟩
  nest (nest n)  ≡⟨ cong nest (nest-x≡0 Nn) ⟩
  nest zero      ≡⟨ nest-0 ⟩
  zero           ∎

-- The nest function is total in its domain (via structural recursion
-- in the domain predicate).
nest-DN : ∀ {d} → Dom d → N (nest d)
nest-DN dom0           = subst N (sym nest-0) zN
nest-DN (domS d h₁ h₂) = subst N (sym (nest-S d)) (nest-DN h₂)

-- The nest function is total.
nest-N : ∀ {n} → N n → N (nest n)
nest-N Nn = subst N (sym (nest-x≡0 Nn)) zN

nest-≤ : ∀ {n} → Dom n → LE (nest n) n
nest-≤ dom0 = nest zero ≤ zero ≡⟨ cong₂ _≤_ nest-0 refl ⟩
              zero ≤ zero      ≡⟨ x≤x zN ⟩
              true             ∎

nest-≤ (domS n h₁ h₂) =
  ≤-trans (nest-N (sN (dom-N n h₁))) (nest-N (dom-N n h₁)) (sN Nn) prf₁ prf₂
    where
    Nn : N n
    Nn = dom-N n h₁

    prf₁ : LE (nest (succ₁ n)) (nest n)
    prf₁ = nest (succ₁ n) ≤ nest n ≡⟨ cong₂ _≤_ (nest-S n) refl ⟩
           nest (nest n) ≤ nest n  ≡⟨ nest-≤ h₂ ⟩
           true                    ∎

    prf₂ : LE (nest n) (succ₁ n)
    prf₂ = ≤-trans (nest-N (dom-N n h₁)) Nn (sN Nn) (nest-≤ h₁) (x≤Sx Nn)

N→Dom : ∀ {n} → N n → Dom n
N→Dom = LT-wfind P ih
  where
  P : D → Set
  P = Dom

  ih : ∀ {x} → N x → (∀ {y} → N y → LT y x → P y) → P x
  ih zN          h = dom0
  ih (sN {x} Nx) h =
    domS x dn-x (h (nest-N Nx ) (x≤y→x<Sy (nest-N Nx) Nx (nest-≤ dn-x)))
      where
      dn-x : Dom x
      dn-x = h Nx (x<Sx Nx)
