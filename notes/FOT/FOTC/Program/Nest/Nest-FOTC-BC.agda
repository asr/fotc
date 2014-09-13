------------------------------------------------------------------------------
-- FOTC version of a nested recursive function by the
-- Bove-Capretta method
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. Vol. 2152 of LNCS. 2001.

module FOT.FOTC.Program.Nest.Nest-FOTC-BC where

open import Common.FOL.Relation.Binary.EqReasoning

open import FOTC.Base

open import FOTC.Data.Nat

import FOTC.Data.Nat.Induction.Acc.WF-I
open FOTC.Data.Nat.Induction.Acc.WF-I.<-WF

open import FOTC.Data.Nat.Inequalities
open import FOTC.Data.Nat.Inequalities.PropertiesI

------------------------------------------------------------------------------
-- The nest function.
postulate
  nest   : D → D
  nest-0 : nest zero            ≡ zero
  nest-S : ∀ d → nest (succ₁ d) ≡ nest (nest d)

data Dom : D → Set where
  dom0 :                              Dom zero
  domS : ∀ d → Dom d → Dom (nest d) → Dom (succ₁ d)

-- Inductive principle associated to the domain predicate.
Dom-ind : (P : D → Set) →
          P zero →
          (∀ {d} → Dom d → P d → Dom (nest d) → P (nest d) → P (succ₁ d)) →
          ∀ {d} → Dom d → P d
Dom-ind P P0 ih dom0           = P0
Dom-ind P P0 ih (domS d h₁ h₂) =
  ih h₁ (Dom-ind P P0 ih h₁) h₂ (Dom-ind P P0 ih h₂)

-- The domain predicate is total.
dom-N : ∀ d → Dom d → N d
dom-N .zero      dom0           = nzero
dom-N .(succ₁ d) (domS d h₁ h₂) = nsucc (dom-N d h₁)

nestCong : ∀ {n₁ n₂} → n₁ ≡ n₂ → nest n₁ ≡ nest n₂
nestCong refl = refl

nest-x≡0 : ∀ {n} → N n → nest n ≡ zero
nest-x≡0 nzero = nest-0
nest-x≡0 (nsucc {n} Nn) =
  nest (succ₁ n) ≡⟨ nest-S n ⟩
  nest (nest n)  ≡⟨ nestCong (nest-x≡0 Nn) ⟩
  nest zero      ≡⟨ nest-0 ⟩
  zero           ∎

-- The nest function is total in its domain (via structural recursion
-- in the domain predicate).
nest-DN : ∀ {d} → Dom d → N (nest d)
nest-DN dom0           = subst N (sym nest-0) nzero
nest-DN (domS d h₁ h₂) = subst N (sym (nest-S d)) (nest-DN h₂)

-- The nest function is total.
nest-N : ∀ {n} → N n → N (nest n)
nest-N Nn = subst N (sym (nest-x≡0 Nn)) nzero

nest-≤ : ∀ {n} → Dom n → nest n ≤ n
nest-≤ dom0 = le (nest zero) zero ≡⟨ leLeftCong nest-0 ⟩
              le zero zero        ≡⟨ x≤x nzero ⟩
              true                ∎

nest-≤ (domS n h₁ h₂) =
  ≤-trans (nest-N (nsucc (dom-N n h₁))) (nest-N (dom-N n h₁)) (nsucc Nn) prf₁ prf₂
    where
    Nn : N n
    Nn = dom-N n h₁

    prf₁ : nest (succ₁ n) ≤ nest n
    prf₁ = le (nest (succ₁ n)) (nest n) ≡⟨ leLeftCong (nest-S n) ⟩
           le (nest (nest n)) (nest n)  ≡⟨ nest-≤ h₂ ⟩
           true                         ∎

    prf₂ : nest n ≤ succ₁ n
    prf₂ = ≤-trans (nest-N (dom-N n h₁)) Nn (nsucc Nn) (nest-≤ h₁) (x≤Sx Nn)

N→Dom : ∀ {n} → N n → Dom n
N→Dom = <-wfind P ih
  where
  P : D → Set
  P = Dom

  ih : ∀ {x} → N x → (∀ {y} → N y → y < x → P y) → P x
  ih nzero          h = dom0
  ih (nsucc {x} Nx) h =
    domS x dn-x (h (nest-N Nx) (x≤y→x<Sy (nest-N Nx) Nx (nest-≤ dn-x)))
      where
      dn-x : Dom x
      dn-x = h Nx (x<Sx Nx)
