------------------------------------------------------------------------------
-- Example of a nested recursive function using the Bove-Capretta
-- method
------------------------------------------------------------------------------

-- Tested with the development version of the standard library on 04
-- April 2011.

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. vol 2152 LNCS. 2001

module NestBC where

open import Data.Nat
open import Data.Nat.Properties

open import Induction.Nat
open import Induction

------------------------------------------------------------------------------

≤′-trans : ∀ {m n o} → m ≤′ n → n ≤′ o → m ≤′ o
≤′-trans ≤′-refl            n≤′o                = n≤′o
≤′-trans (≤′-step {n} m≤′n) ≤′-refl             = ≤′-step m≤′n
≤′-trans (≤′-step {n} m≤′n) (≤′-step {o} Sn≤′o) =
  ≤′-step (≤′-trans m≤′n (≤′-trans (≤′-step ≤′-refl) Sn≤′o))

mutual
  -- The domain predicate of the nest function.
  data DomNest : ℕ → Set where
    dom0 : DomNest 0
    domS : ∀ {n} → (h₁ : DomNest n) →
                   (h₂ : DomNest (nestD n h₁)) →
                   DomNest (suc n)

  -- The nest function by structural recursion on the domain predicate.
  nestD : ∀ n → DomNest n → ℕ
  nestD .0       dom0             = 0
  nestD .(suc n) (domS {n} h₁ h₂) = nestD (nestD n h₁) h₂

nestD-≤′ : ∀ n → (h : DomNest n) → nestD n h ≤′ n
nestD-≤′ .0       dom0             = ≤′-refl
nestD-≤′ .(suc n) (domS {n} h₁ h₂) =
  ≤′-trans (≤′-trans (nestD-≤′ (nestD n h₁) h₂) (nestD-≤′ n h₁))
           (≤′-step ≤′-refl)

-- The nest function is total.
allDomNest : ∀ n → DomNest n
allDomNest = build <-rec-builder P ih
  where
    P : ℕ → Set
    P = DomNest

    ih : ∀ y → <-Rec P y → P y
    ih zero    rec = dom0
    ih (suc y) rec = domS dn-y (rec (nestD y dn-y) (s≤′s (nestD-≤′ y dn-y)))
        where
          helper : (x : ℕ) → x <′ y → P x
          helper x Sx≤′y = rec x (≤′-step Sx≤′y)

          dn-y : DomNest y
          dn-y = ih y helper

-- The nest function.
nest : ℕ → ℕ
nest n = nestD n (allDomNest n)
