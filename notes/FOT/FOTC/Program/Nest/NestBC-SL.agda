------------------------------------------------------------------------------
-- Example of a nested recursive function using the Bove-Capretta
-- method
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K #-}

-- From: Ana Bove and Venanzio Capretta. Nested general recursion and
-- partiality in type theory. vol 2152 LNCS. 2001.

module FOT.FOTC.Program.Nest.NestBC-SL where

open import Data.Nat renaming ( suc to succ )
open import Data.Nat.Properties

open import Induction
open import Induction.Nat

open import Relation.Binary

module NDTO = DecTotalOrder decTotalOrder

------------------------------------------------------------------------------

-- The original non-terminating function.

{-# NO_TERMINATION_CHECK #-}
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