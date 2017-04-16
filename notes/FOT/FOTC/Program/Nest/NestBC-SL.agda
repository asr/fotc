------------------------------------------------------------------------------
-- Example of a nested recursive function using the Bove-Capretta
-- method
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

-- From: Bove, A. and Capretta, V. (2001). Nested General Recursion
-- and Partiality in Type Theory. In: Theorem Proving in Higher Order
-- Logics (TPHOLs 2001). Ed. by Boulton, R. J. and Jackson,
-- P. B. Vol. 2152. LNCS. Springer, pp. 121–135.

module FOT.FOTC.Program.Nest.NestBC-SL where

open import Data.Nat renaming ( suc to succ )
open import Data.Nat.Properties

open import Induction
open import Induction.Nat

open import Relation.Binary

module NDTO = DecTotalOrder ≤-decTotalOrder

------------------------------------------------------------------------------
-- The original non-terminating function.

{-# TERMINATING #-}
nestI : ℕ → ℕ
nestI 0        = 0
nestI (succ n) = nestI (nestI n)

≤′-trans : Transitive _≤′_
≤′-trans i≤′j j≤′k = ≤⇒≤′ (NDTO.trans (≤′⇒≤ i≤′j) (≤′⇒≤ j≤′k))

mutual
  -- The domain predicate of the nest function.
  data NestDom : ℕ → Set where
    nestDom0 : NestDom 0
    nestDomS : ∀ {n} → (h₁ : NestDom n) →
               (h₂ : NestDom (nestD n h₁)) →
               NestDom (succ n)

  -- The nest function by structural recursion on the domain predicate.
  nestD : ∀ n → NestDom n → ℕ
  nestD .0        nestDom0             = 0
  nestD .(succ n) (nestDomS {n} h₁ h₂) = nestD (nestD n h₁) h₂

nestD-≤′ : ∀ n → (h : NestDom n) → nestD n h ≤′ n
nestD-≤′ .0        nestDom0             = ≤′-refl
nestD-≤′ .(succ n) (nestDomS {n} h₁ h₂) =
  ≤′-trans (≤′-trans (nestD-≤′ (nestD n h₁) h₂) (nestD-≤′ n h₁))
           (≤′-step ≤′-refl)

-- The nest function is total.
allNestDom : ∀ n → NestDom n
allNestDom = build <-rec-builder P ih
  where
  P : ℕ → Set
  P = NestDom

  ih : ∀ y → <-Rec P y → P y
  ih zero     rec = nestDom0
  ih (succ y) rec = nestDomS nd-y (rec (nestD y nd-y) (s≤′s (nestD-≤′ y nd-y)))
    where
    helper : ∀ x → x <′ y → P x
    helper x Sx≤′y = rec x (≤′-step Sx≤′y)

    nd-y : NestDom y
    nd-y = ih y helper

-- The nest function.
nest : ℕ → ℕ
nest n = nestD n (allNestDom n)
